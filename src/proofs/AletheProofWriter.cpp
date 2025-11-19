/*********************                                                        */
/*! \file AletheProofWriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Omri Isac, Guy Katz
 ** This file is part of the Marabou project.
 ** Copyright (c) 2017-2025 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved. See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 **/

#include "AletheProofWriter.h"

AletheProofbWriter::AletheProofbWriter( unsigned explanationSize,
                                        const Vector<double> &upperBounds,
                                        const Vector<double> &lowerBounds,
                                        const SparseMatrix *tableau,
                                        const List<PiecewiseLinearConstraint *> &problemConstraints,
                                        UnsatCertificateNode *root )
    : _initialTableau( tableau )
    , _plc( problemConstraints )
    , _root( root )
    , _n( upperBounds.size() )
    , _m( explanationSize )
    , _stepCounter( 0 )
    , _lemmaCounter( 0 )
{
    for ( unsigned i = 0; i < _n; ++i )
    {
        _currentLowerBounds.append( Stack<std::tuple<int, double>>() );
        _currentUpperBounds.append( Stack<std::tuple<int, double>>() );

        _currentLowerBounds[i].push( std::tuple<int, double>( 0, lowerBounds[i] ) );
        _currentUpperBounds[i].push( std::tuple<int, double>( 0, upperBounds[i] ) );
    }
}

void AletheProofbWriter::writeAssumptions()
{
    ASSERT( _proof.empty() );
    Vector<double> ubs;
    Vector<double> lbs;
    insertCurrentBoundsToVec( true, ubs );
    insertCurrentBoundsToVec( false, lbs );

    List<String> smtLib =
        SmtLibWriter::convertToSmtLib( _m, _n, ubs, lbs, _initialTableau, List<Equation>(), _plc );

    unsigned counter = 0;
    String assumptionTitle;
    bool isTableau;

    // Convert assertions to assumptions
    for ( auto line : smtLib )
    {
        // Ignore header and footer
        if ( line.contains( "declare" ) || line.contains( "set-logic" ) ||
             line.contains( "check" ) || line.contains( "exit" ) )
            continue;

        isTableau = false;
        if ( counter < _n )
        {
            ASSERT( line.contains( "<=" ) );
            assumptionTitle = "u" + std::to_string( counter ) + ".0";
        }
        else if ( counter < 2 * _n )
        {
            ASSERT( line.contains( ">=" ) );
            assumptionTitle = "l" + std::to_string( counter - _n ) + ".0";
        }
        else if ( counter < 2 * _n + _m )
        {
            ASSERT( line.contains( " = " ) );
            assumptionTitle = "e" + std::to_string( counter - ( 2 * _n ) );
            isTableau = true;
        }
        else
        {
            continue;
        }


        ++counter;


        line.replace( "assert ", String( "assume " ) + assumptionTitle + " " );
        _proof.append( line );


        if ( isTableau )
            _tableauAssumptions.append( line );
    }

    List<String> plcAssumptions = List<String>();
    List<String> plcSplits = List<String>();
    for ( const auto &plc : _plc )
    {
        List<PiecewiseLinearCaseSplit> splitsInFixedOrder = List<PiecewiseLinearCaseSplit>();
        const PiecewiseLinearCaseSplit &backChildTightening = plc->getCaseSplits().back();

        // Insert the inactive phase first
        if ( isSplitActive( backChildTightening ) )
        {
            splitsInFixedOrder.append( plc->getCaseSplits().back() );
            splitsInFixedOrder.append( plc->getCaseSplits().front() );
        }
        else
        {
            splitsInFixedOrder.append( plc->getCaseSplits().front() );
            splitsInFixedOrder.append( plc->getCaseSplits().back() );
        }

        String constraintNum = std::to_string( plc->getTableauAuxVars().front() );
        String plcAssumption = String( "( assume plc" ) + constraintNum + " ( or " +
                               getSplitsAsClause( splitsInFixedOrder ) + ")  )\n";

        plcAssumptions.append( plcAssumption );

        String plcSplit = String( "( step split" ) + constraintNum + " (cl " +
                          getSplitsAsClause( splitsInFixedOrder ) + ") :rule or :premises ( plc" +
                          constraintNum + " ) )\n";
        plcSplits.append( plcSplit );

        for ( const auto &split : plc->getCaseSplits() )
        {
            unsigned innerCounter = 0;
            String isActive = isSplitActive( split ) ? "a" : "i";
            for ( const auto &bound : split.getBoundTightenings() )
            {
                String line = String( "( step split" ) + constraintNum + "_" + isActive +
                              std::to_string( innerCounter ) + " (cl ( not " +
                              getSplitAsClause( split ) + " )" + getBoundAsClause( bound ) +
                              " ) :rule and_pos :args( " + std::to_string( innerCounter ) +
                              " ) )\n";
                plcSplits.append( line );

                ++innerCounter;
            }
        }
    }

    _proof.append( plcAssumptions );
    _proof.append( plcSplits );
}

void AletheProofbWriter::writeAletheProof( IFile &file )
{
    writeAssumptions();

    writeAletheProof( _root );

    // Wrap-up everything and write to a file
    writeInstanceToFile( file, _proof );
}

unsigned AletheProofbWriter::writeAletheProof( const UnsatCertificateNode *node )
{
    for ( const auto &bound : node->getSplit().getBoundTightenings() )
        if ( bound._type == Tightening::UB )
            _currentUpperBounds[bound._variable].push(
                std::tuple<int, double>( -1, bound._value ) );
        else
            _currentLowerBounds[bound._variable].push(
                std::tuple<int, double>( -1, bound._value ) );

    applyAllLemmas( node );

    if ( node->isValidLeaf() )
        applyContradiction( node );
    else if ( node->isValidNonLeaf() )
    {
        List<unsigned> childrenIndices = List<unsigned>();
        for ( const auto &child : node->getChildren() )
            childrenIndices.append( writeAletheProof( child ) - 1 );

        concludeChildrenUnsat( node, _stepCounter, childrenIndices );
    }

    for ( const auto &lemma : node->getPLCLemmas() )
        if ( lemma.get() ) // TODO && lemma->getToCheck() )
        {
            Tightening::BoundType causingBound = lemma->getCausingVarBound();
            Tightening::BoundType affectedBound = lemma->getAffectedVarBound();
            if ( causingBound == Tightening::UB )
                _currentUpperBounds[lemma->getCausingVars().front()].pop();
            else
                _currentLowerBounds[lemma->getCausingVars().front()].pop();

            if ( affectedBound == Tightening::UB )
                _currentUpperBounds[lemma->getAffectedVar()].pop();
            else
                _currentLowerBounds[lemma->getAffectedVar()].pop();
        }
    for ( const auto &bound : node->getSplit().getBoundTightenings() )
        if ( bound._type == Tightening::UB )
            _currentUpperBounds[bound._variable].pop();
        else
            _currentLowerBounds[bound._variable].pop();

    return ++_stepCounter;
}

unsigned AletheProofbWriter::applyContradiction( const UnsatCertificateNode *node )
{
    ASSERT( node->isValidLeaf() );
    const SparseUnsortedList &contradiction = node->getContradiction()->getContradiction();
    String farkasArgs = "";
    String farkasClause = "";
    String farkasParticipants = "";

    farkasStrings( contradiction, farkasArgs, farkasClause, farkasParticipants, -1, true );
    farkasClause += ")";
    farkasArgs += ") )\n";

    String laGeneric = String( "( step t" + std::to_string( _stepCounter ) ) + " " + farkasClause +
                       " :rule la_generic :args " + farkasArgs;

    String res = String( "( step res" + std::to_string( _stepCounter ) ) + " (cl " +
                 getPathClause( node ) + ") :rule resolution :premises (" +
                 getPathResSteps( node ) + " t" + std::to_string( _stepCounter ) + " " +
                 farkasParticipants + " ) ) \n";


    _proof.append( laGeneric );
    _proof.append( res );
    return _stepCounter;
}

void AletheProofbWriter::writeInstanceToFile( IFile &file, const List<String> &instance )
{
    file.open( File::MODE_WRITE_TRUNCATE );

    for ( const String &s : instance )
        file.write( s );

    file.close();
}

void AletheProofbWriter::insertCurrentBoundsToVec( bool isUpper, Vector<double> &boundsVec )
{
    Vector<Stack<std::tuple<int, double>>> &temp =
        isUpper ? _currentUpperBounds : _currentLowerBounds;

    boundsVec = Vector<double>( _n, 0 );
    for ( unsigned i = 0; i < _n; ++i )
        boundsVec[i] = std::get<1>( temp[i].top() );
}

void AletheProofbWriter::concludeChildrenUnsat( const UnsatCertificateNode *node,
                                                unsigned i,
                                                List<unsigned> childrenIndices )
{
    ASSERT( node->isValidNonLeaf() );
    ASSERT( childrenIndices.size() == 2 )
    PiecewiseLinearCaseSplit firstChildSplit = node->getChildren().front()->getSplit();
    String resLine = String( "( step res" + std::to_string( i ) + " (cl " ) +
                     getPathClause( node ) + ") :rule resolution :premises ( split" +
                     std::to_string( node->getChildren().front()->getSplitNum() ) + " res" +
                     std::to_string( childrenIndices.front() ) + " res" +
                     std::to_string( childrenIndices.back() ) + ") )\n";

    _proof.append( resLine );
}

String AletheProofbWriter::getPathClause( const UnsatCertificateNode *node )
{
    if ( !node->getParent() )
        return "";

    String clause = "";
    const UnsatCertificateNode *cur = node;
    while ( !cur->getSplit().getBoundTightenings().empty() )
    {
        clause += "( not ( and ";
        const PiecewiseLinearCaseSplit &headSplit = cur->getSplit();
        for ( const auto bound : headSplit.getBoundTightenings() )
            clause += getBoundAsClause( bound );
        cur = cur->getParent();
        clause += " ) )";
    }
    return clause;
}

String AletheProofbWriter::getBoundAsClause( const Tightening &bound )
{
    if ( bound._type == Tightening::UB )
        return String( "( <= x" + std::to_string( bound._variable ) + " " ) +
               SmtLibWriter::signedValue( bound._value ) + ")";

    return String( "( >= x" + std::to_string( bound._variable ) + " " ) +
           SmtLibWriter::signedValue( bound._value ) + ")";
}


String AletheProofbWriter::getSplitAsClause( const PiecewiseLinearCaseSplit &split )
{
    ASSERT( split.getEquations().empty() );
    String clause = "( and ";
    for ( const auto &bound : split.getBoundTightenings() )
        clause += getBoundAsClause( bound );

    clause += ") ";
    return clause;
}

String AletheProofbWriter::getSplitsAsClause( const List<PiecewiseLinearCaseSplit> &splits )
{
    String clause = "";
    for ( const auto &split : splits )
        clause += getSplitAsClause( split );
    return clause;
}

bool AletheProofbWriter::isSplitActive( const PiecewiseLinearCaseSplit &split )
{
    ASSERT( split.getEquations().empty() )
    return split.getBoundTightenings().back()._type == Tightening::LB ||
           split.getBoundTightenings().front()._type == Tightening::LB;
}

String AletheProofbWriter::getPathResSteps( const UnsatCertificateNode *node )
{
    if ( !node->getParent() )
        return "";

    String resSteps = " ";
    const UnsatCertificateNode *cur = node;
    while ( !cur->getSplit().getBoundTightenings().empty() )
    {
        String currentStep = " split" + std::to_string( cur->getSplitNum() );
        const PiecewiseLinearCaseSplit &headSplit = cur->getSplit();
        String isActive = isSplitActive( headSplit ) ? "a" : "i";

        for ( unsigned i = 0; i < headSplit.getBoundTightenings().size(); ++i )
            currentStep += String( " split" + std::to_string( cur->getSplitNum() ) + "_" ) +
                           isActive + std::to_string( i );
        cur = cur->getParent();
        // Add steps to the left
        resSteps = currentStep + resSteps;
    }

    return resSteps;
}
void AletheProofbWriter::applyAllLemmas( const UnsatCertificateNode *node )
{
    List<unsigned> participatingVars;
    PiecewiseLinearConstraint *matchedConstraint = NULL;

    for ( const auto &lemma : node->getPLCLemmas() )
    {
        if ( !lemma.get() ) // TODO || !lemma->getToCheck() )
            continue;
        // Make sure propagation was made by a problem constraint
        for ( const auto &constraint : _plc )
        {
            if ( constraint->getType() != lemma->getConstraintType() )
                continue;

            participatingVars = constraint->getParticipatingVariables();

            if ( participatingVars.exists( lemma->getAffectedVar() ) )
                matchedConstraint = constraint;
        }

        // TODO add support for all types of PLCs
        if ( matchedConstraint && matchedConstraint->getType() == RELU )
            applyReluLemma( node, *lemma, (ReluConstraint *)matchedConstraint );
    }
}
void AletheProofbWriter::applyReluLemma( const UnsatCertificateNode *node,
                                         const PLCLemma &lemma,
                                         ReluConstraint *plc )
{
    ASSERT( plc != NULL );

    // TODO check if they are b f aux for some plc arg
    unsigned causingVar = lemma.getCausingVars().front();
    unsigned affectedVar = lemma.getAffectedVar();
    unsigned targetBound = lemma.getMinTargetBound();
    double bound = lemma.getBound();
    const List<SparseUnsortedList> &explanations = lemma.getExplanations();
    Tightening::BoundType causingVarBound = lemma.getCausingVarBound();
    Tightening::BoundType affectedVarBound = lemma.getAffectedVarBound();

    ASSERT( explanations.size() == 1 );

    //    String tempString = getBoundAsClause( Tightening( causingVar, bound, causingVarBound ) ) +
    //                        " ( not " +
    //                        getBoundAsClause( Tightening( causingVar, bound, causingVarBound ) ) +
    //                        ")";
    //
    //    String taut = String( "(step taut" + std::to_string( _lemmaCounter ) + "( cl ( or " ) +
    //                  tempString + ") ) :rule la_tautology)\n";
    //    String tautSplit = String( "( step split" ) + std::to_string( _lemmaCounter ) + " (cl " +
    //                       tempString + ") :rule or :premises ( taut" +
    //                       std::to_string( _lemmaCounter ) + " ) )\n";


    String farkasArgs = "";
    String farkasClause = "";
    String farkasParticipants = "";

    farkasStrings( explanations.front(),
                   farkasArgs,
                   farkasClause,
                   farkasParticipants,
                   causingVar,
                   causingVarBound == Tightening::UB );

    farkasClause += getBoundAsClause( Tightening( causingVar, targetBound, causingVarBound ) );

    farkasArgs += " 1 ";
    farkasClause += ")";
    farkasArgs += ") )\n";

    String laGeneric = String( "( step farkasLem" + std::to_string( _lemmaCounter ) ) + " " +
                       farkasClause + " :rule la_generic :args " + farkasArgs;

    String res = String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " (cl " +
                 getPathClause( node ) +
                 getBoundAsClause( Tightening( causingVar, targetBound, causingVarBound ) ) +
                 ") :rule resolution :premises (" + getPathResSteps( node ) + " farkasLem" +
                 std::to_string( _lemmaCounter ) + " " + farkasParticipants + " ) ) \n";

    Vector<Stack<std::tuple<int, double>>> &causingTempVec =
        ( causingVarBound == Tightening::UB ) ? _currentUpperBounds : _currentLowerBounds;

    causingTempVec[causingVar].push( std::tuple<int, double>( _lemmaCounter, targetBound ) );

    ++_lemmaCounter;
    // TODO prove by each lemma type
    unsigned b = plc->getB();
    unsigned f = plc->getF();
    unsigned aux = plc->getAux();
    unsigned identifier = plc->getTableauAuxVars().front();

    String proofRule = "";
    String proofRuleRes = "";
    unsigned eqIndex = plc->getTableauAuxVars().front() - _n + _m;

    String lineLiteral = convertTableauAssumptionToClause( eqIndex );
    String counterPartBound = String( " ( not " ) +
                              getBoundAsClause( Tightening( identifier, 0, Tightening::UB ) ) +
                              ") ";

    String proofClause =
        String( "( not " ) +
        getBoundAsClause( Tightening( causingVar, targetBound, causingVarBound ) ) + ") " +
        getBoundAsClause( Tightening( affectedVar, bound, affectedVarBound ) );

    proofClause += lineLiteral;
    proofClause += counterPartBound;

    if ( (causingVar == f || causingVar == b) && causingVarBound == Tightening::LB && affectedVar == aux &&
         affectedVarBound == Tightening::UB && targetBound > 0 )
    {
        //        String temp =
        //            String( "( not " ) + getBoundAsClause( Tightening( b, 0, Tightening::LB ) ) +
        //            ") ";
        //
        //        proofClause += temp;
        //        proofRule = String( "( step farkasLem" + std::to_string( _lemmaCounter ) ) + "( cl
        //        " +
        //                    proofClause + ") :rule la_generic :args (1 1 1 -1 1) )\n";
        //

        String tempString =
            String( "( not " ) + getBoundAsClause( Tightening( causingVar, 0, Tightening::UB ) ) +
            ") ( not " + getBoundAsClause( Tightening( causingVar, targetBound, Tightening::LB ) ) +
            ")";

        proofRule = String( "( step taut" + std::to_string( _lemmaCounter ) + "( cl ( or " ) +
                    tempString + ") ) :rule la_tautology)\n";
        proofRule += String( "( step tautSplit" ) + std::to_string( _lemmaCounter ) + " (cl " +
                     tempString + ") :rule or :premises ( taut" + std::to_string( _lemmaCounter ) +
                     " ) )\n";

        proofRuleRes = String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " ( cl " +
                       getPathClause( node ) +
                       getBoundAsClause( Tightening( affectedVar, bound, affectedVarBound ) ) +
                       ") :rule resolution :premises ( resLem" +
                       std::to_string( _lemmaCounter - 1 ) + " tautSplit" +
                       std::to_string( _lemmaCounter ) + " split" + std::to_string( identifier ) +
                       "_i1 split" + std::to_string( identifier ) + " split" +
                       std::to_string( identifier ) + "_a1 ) ) \n";

        // TODO move to bottom
        Vector<Stack<std::tuple<int, double>>> &affectedTempVec =
            ( affectedVarBound == Tightening::UB ) ? _currentUpperBounds : _currentLowerBounds;

        affectedTempVec[affectedVar].push( std::tuple<int, double>( _lemmaCounter, bound ) );
    }

    /*
    // If lb of b is non negative, then ub of aux is 0
    if ( causingVar == b && causingVarBound == Tightening::LB && affectedVar == aux &&
         affectedVarBound == Tightening::UB && !FloatUtils::isNegative( explainedBound + epsilon ) )
        return 0;

    // If lb of f is positive, then ub if aux is 0
    else if ( causingVar == f && causingVarBound == Tightening::LB && affectedVar == aux &&
              affectedVarBound == Tightening::UB &&
              FloatUtils::isPositive( explainedBound + epsilon ) )
        return 0;

    // If lb of b is negative x, then ub of aux is -x
    else if ( causingVar == b && causingVarBound == Tightening::LB && affectedVar == aux &&
              affectedVarBound == Tightening::UB &&
              FloatUtils::isNegative( explainedBound - epsilon ) )
        return -explainedBound;

    // If lb of aux is positive, then ub of f is 0
    else if ( causingVar == aux && causingVarBound == Tightening::LB && affectedVar == f &&
              affectedVarBound == Tightening::UB &&
              FloatUtils::isPositive( explainedBound + epsilon ) )
        return 0;

    // If lb of f is negative, then it is 0
    else if ( causingVar == f && causingVarBound == Tightening::LB && affectedVar == f &&
              affectedVarBound == Tightening::LB &&
              FloatUtils::isNegative( explainedBound - epsilon ) )
        return 0;

    // Propagate ub from f to b
    else if ( causingVar == f && causingVarBound == Tightening::UB && affectedVar == b &&
              affectedVarBound == Tightening::UB )
        return explainedBound;

    // If ub of b is non positive, then ub of f is 0
    else if ( causingVar == b && causingVarBound == Tightening::UB && affectedVar == f &&
              affectedVarBound == Tightening::UB &&
              !FloatUtils::isPositive( explainedBound - epsilon ) )
        return 0;

    // If ub of b is non positive x, then lb of aux is -x
    else if ( causingVar == b && causingVarBound == Tightening::UB && affectedVar == aux &&
              affectedVarBound == Tightening::LB &&
              !FloatUtils::isPositive( explainedBound - epsilon ) )
        return -explainedBound;

    // If ub of b is positive, then propagate to f ( positivity of explained bound is not checked
    // since negative explained ub can always explain positive bound )
    else if ( causingVar == b && causingVarBound == Tightening::UB && affectedVar == f &&
              affectedVarBound == Tightening::UB &&
              FloatUtils::isPositive( explainedBound + epsilon ) )
        return explainedBound;

    // If ub of aux is x, then lb of b is -x
    else if ( causingVar == aux && causingVarBound == Tightening::UB && affectedVar == b &&
              affectedVarBound == Tightening::LB )
        return -explainedBound;
    */


    _proof.append( laGeneric );
    _proof.append( res );
    _proof.append( proofRule );
    _proof.append( proofRuleRes );

    ++_lemmaCounter;
}

void AletheProofbWriter::linearCombinationMpq( const std::vector<mpq_t> &explainedRow,
                                               const SparseUnsortedList &expl )
{
    SparseUnsortedList tableauRow( _n );
    for ( const auto &entry : expl )
    {
        if ( entry._value == 0 )
            continue;

        _initialTableau->getRow( entry._index, &tableauRow );
        for ( const auto &tableauEntry : tableauRow )
        {
            if ( tableauEntry._value != 0 )
            {
                mpq_t tempval, tempEntry, tempTableauEntry;
                mpq_init( tempval );
                mpq_init( tempEntry );
                mpq_init( tempTableauEntry );
                mpq_set_d( tempTableauEntry, tableauEntry._value );
                mpq_set_d( tempEntry, entry._value );
                mpq_mul( tempval, tempEntry, tempTableauEntry );
                mpq_add( const_cast<mpq_ptr>( explainedRow[tableauEntry._index] ),
                         explainedRow[tableauEntry._index],
                         tempval );
                mpq_clear( tempval );
                mpq_clear( tempEntry );
                mpq_clear( tempTableauEntry );
            }
        }
    }
}

void AletheProofbWriter::farkasStrings( const SparseUnsortedList &expl,
                                        String &farkasArgs,
                                        String &farkasClause,
                                        String &farkasParticipants,
                                        int explainedVar,
                                        bool isUpper )
{
    std::vector<mpq_t> explainedRow = std::vector<mpq_t>( _n );
    for ( const auto num : explainedRow )
        mpq_init( num );

    linearCombinationMpq( explainedRow, expl );
    if ( explainedVar > 0 )
    {
        mpq_t temp;
        mpq_init( temp );
        int val = isUpper ? 1 : -1;
        mpq_set_d( temp, val );
        mpq_add(
            const_cast<mpq_ptr>( explainedRow[explainedVar] ), explainedRow[explainedVar], temp );
        mpq_clear( temp );
    }

    farkasClause = "(cl ";
    farkasArgs = "( ";
    farkasParticipants = "";

    for ( const auto entry : expl )
        if ( entry._value != 0 )
        {
            farkasClause += convertTableauAssumptionToClause( entry._index );

            mpq_class temp( -entry._value );
            farkasArgs += temp.get_str() + " ";
            farkasParticipants += String( "e" + std::to_string( entry._index ) ) + " ";
        }

    for ( unsigned i = 0; i < _n; ++i )
    {
        mpq_class temp( explainedRow[i] );
        if ( mpq_sgn( explainedRow[i] ) > 0 )
        {
            farkasClause +=
                String( "( not ( <= x" + std::to_string( i ) ) + String( " " ) +
                SmtLibWriter::signedValue( std::get<1>( _currentUpperBounds[i].top() ) ) + " ) ) ";
            farkasArgs += temp.get_str() + " ";

            if ( std::get<0>( _currentUpperBounds[i].top() ) == 0 )
                farkasParticipants +=
                    String( "u" + std::to_string( i ) + "." +
                            std::to_string( std::get<0>( _currentUpperBounds[i].top() ) ) ) +
                    " ";
            else if ( std::get<0>( _currentUpperBounds[i].top() ) > 0 )
                farkasParticipants +=
                    String( "resLem" +
                            std::to_string( std::get<0>( _currentUpperBounds[i].top() ) ) ) +
                    " ";
        }
        else if ( mpq_sgn( explainedRow[i] ) < 0 )
        {
            farkasClause +=
                String( "( not ( >= x" + std::to_string( i ) ) + String( " " ) +
                SmtLibWriter::signedValue( std::get<1>( _currentLowerBounds[i].top() ) ) + " ) ) ";
            farkasArgs += temp.get_str() + " ";

            if ( std::get<0>( _currentLowerBounds[i].top() ) == 0 )
                farkasParticipants +=
                    String( "l" + std::to_string( i ) + "." +
                            std::to_string( std::get<0>( _currentLowerBounds[i].top() ) ) ) +
                    " ";
            else if ( std::get<0>( _currentLowerBounds[i].top() ) > 0 )
                farkasParticipants +=
                    String( "resLem" +
                            std::to_string( std::get<0>( _currentLowerBounds[i].top() ) ) ) +
                    " ";
        }
    }


    for ( const auto num : explainedRow )
        mpq_clear( num );
}


String AletheProofbWriter::convertTableauAssumptionToClause( unsigned index )
{
    String assumption( _tableauAssumptions[index] );
    unsigned begin = assumption.find( "=" );
    return String( "(not ( " ) + assumption.substring( begin, assumption.length() - begin - 1 ) +
           " ";
}
