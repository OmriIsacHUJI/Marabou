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
    , _lemmaCounter( 1 )
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

    writePLCAssumption();
}

void AletheProofbWriter::writePLCAssumption()
{
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

        plcAssumption +=
            String( "( assume i" ) + constraintNum +
            " ( = " + getBoundAsClause( splitsInFixedOrder.back().getBoundTightenings().front() ) +
            " " + getBoundAsClause( splitsInFixedOrder.back().getBoundTightenings().back() ) +
            " ) )\n";

        plcAssumption +=
            String( "( assume a" ) + constraintNum +
            " ( = " + getBoundAsClause( splitsInFixedOrder.front().getBoundTightenings().front() ) +
            " " + getBoundAsClause( splitsInFixedOrder.front().getBoundTightenings().back() ) +
            " ) )\n";

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
                              getSplitAsClause( split ) + " ) " + getBoundAsClause( bound ) +
                              " ) :rule and_pos :args( " + std::to_string( innerCounter ) +
                              " ) )\n";
                plcSplits.append( line );

                ++innerCounter;
            }

            if ( plc->getType() == RELU )
            {
                String line1 = String( "( step equiv" ) + constraintNum + "_" + isActive +
                             +"0 (cl ( not " +
                               getBoundAsClause( split.getBoundTightenings().front() ) + +" ) " +
                               getBoundAsClause( split.getBoundTightenings().back() ) +
                               " ) :rule equiv1 :premises( " + isActive + constraintNum + " ) )\n";

                String line2 = String( "( step equiv" ) + constraintNum + "_" + isActive +
                             +"1 (cl " + getBoundAsClause( split.getBoundTightenings().front() ) +
                             +" (not " + getBoundAsClause( split.getBoundTightenings().back() ) +
                               " ) ) :rule equiv2 :premises( " + isActive + constraintNum +
                               " ) )\n";
                plcSplits.append( line1 );
                plcSplits.append( line2 );
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
    else if ( node->getDelegationStatus() != DONT_DELEGATE )
        writeDelegatedLeaf( node );
    else if ( node->isValidNonLeaf() )
    {
        List<unsigned> childrenIndices = List<unsigned>();
        for ( const auto &child : node->getChildren() )
            childrenIndices.append( writeAletheProof( child ) - 1 );

        concludeChildrenUnsat( node, _stepCounter, childrenIndices );
    }

    for ( const auto &lemma : node->getPLCLemmas() )
        if ( lemma.get() && lemma->getToCheck() )
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
        if ( !lemma.get() || !lemma->getToCheck() )
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

    unsigned causingVar = lemma.getCausingVars().front();
    unsigned affectedVar = lemma.getAffectedVar();
    double targetBound = lemma.getMinTargetBound();
    double bound = lemma.getBound();
    const List<SparseUnsortedList> &explanations = lemma.getExplanations();
    Tightening::BoundType causingVarBound = lemma.getCausingVarBound();
    Tightening::BoundType affectedVarBound = lemma.getAffectedVarBound();

    // If bound is not tighter, return
    if ( ( affectedVarBound == Tightening::UB &&
           bound > std::get<1>( _currentUpperBounds[affectedVar].top() ) ) ||
         ( affectedVarBound == Tightening::LB &&
           bound < std::get<1>( _currentLowerBounds[affectedVar].top() ) ) )
        return;

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
    String causeBound = getBoundAsClause( Tightening( causingVar, targetBound, causingVarBound ) );

    farkasStrings( explanations.front(),
                   farkasArgs,
                   farkasClause,
                   farkasParticipants,
                   causingVar,
                   causingVarBound == Tightening::UB );

    farkasClause += causeBound;

    farkasArgs += " 1 ";
    farkasClause += ")";
    farkasArgs += ") )\n";

    String laGeneric = String( "( step farkasLem" + std::to_string( _lemmaCounter ) ) + " " +
                       farkasClause + " :rule la_generic :args " + farkasArgs;

    String res = String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " (cl " +
                 getPathClause( node ) + causeBound + ") :rule resolution :premises (" +
                 getPathResSteps( node ) + " farkasLem" + std::to_string( _lemmaCounter ) + " " +
                 farkasParticipants + " ) ) \n";

    Vector<Stack<std::tuple<int, double>>> &causingTempVec =
        ( causingVarBound == Tightening::UB ) ? _currentUpperBounds : _currentLowerBounds;

    // Use opportunity to learn a better bound
    double betterBound =
        ( causingVarBound == Tightening::UB )
            ? FloatUtils::min( std::get<1>( causingTempVec[causingVar].top() ), targetBound )
            : FloatUtils::max( std::get<1>( causingTempVec[causingVar].top() ), targetBound );

    causingTempVec[causingVar].push( std::tuple<int, double>( _lemmaCounter, betterBound ) );

    ++_lemmaCounter;

    unsigned b = plc->getB();
    unsigned f = plc->getF();
    unsigned aux = plc->getAux();
    String identifier = std::to_string( plc->getTableauAuxVars().front() );
    bool matched = false;

    String proofRule = "";
    String proofRuleRes = "";
    String tempString = "";

    if ( targetBound > 0 )
        tempString += String( "( not " ) +
                      getBoundAsClause( Tightening( causingVar, 0, Tightening::UB ) ) + ") ( not " +
                      causeBound + ") ";
    else if ( targetBound < 0 )
        tempString += String( "( not" ) + causeBound + ") ( not " +
                      getBoundAsClause( Tightening( causingVar, 0, Tightening::LB ) ) + ") ";

    if ( targetBound != 0 )
    {
        proofRule = String( "( step taut" + std::to_string( _lemmaCounter ) + "( cl ( or " ) +
                    tempString + ") ) :rule la_tautology)\n";
        proofRule += String( "( step tautSplit" ) + std::to_string( _lemmaCounter ) + " (cl " +
                     tempString + ") :rule or :premises ( taut" + std::to_string( _lemmaCounter ) +
                     " ) )\n";
    }
    String conclusion = getBoundAsClause( Tightening( affectedVar, bound, affectedVarBound ) );

    if ( ( causingVar == f || causingVar == b ) && causingVarBound == Tightening::LB &&
         affectedVar == aux && affectedVarBound == Tightening::UB && targetBound > 0 )
    {
        matched = true;
        String splitrule = causingVar == f ? "_i1" : "_i0";
        proofRuleRes = String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " ( cl " +
                       getPathClause( node ) + conclusion +
                       ") :rule resolution :premises ( resLem" +
                       std::to_string( _lemmaCounter - 1 ) + " tautSplit" +
                       std::to_string( _lemmaCounter ) + " split" + identifier + splitrule +
                       " split" + identifier + " split" + identifier + "_a1 ) ) \n";
    }
    else if ( causingVar == b && causingVarBound == Tightening::LB && affectedVar == aux &&
              affectedVarBound == Tightening::UB && targetBound == 0 )
    {
        matched = true;
        proofRuleRes = String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " ( cl " +
                       getPathClause( node ) + conclusion +
                       ") :rule resolution :premises ( resLem" +
                       std::to_string( _lemmaCounter - 1 ) + " equiv" + identifier + "_a0) ) \n";
    }
    // If lb of aux is positive, then ub of f is 0
    else if ( causingVar == aux && causingVarBound == Tightening::LB && affectedVar == f &&
              affectedVarBound == Tightening::UB && targetBound > 0 )
    {
        matched = true;

        proofRuleRes =
            String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " ( cl " +
            getPathClause( node ) + conclusion + ") :rule resolution :premises ( resLem" +
            std::to_string( _lemmaCounter - 1 ) + " tautSplit" + std::to_string( _lemmaCounter ) +
            " split" + identifier + "_a1 split" + identifier + " split" + identifier + "_i1 ) ) \n";
    }

    // If ub of b is non positive, then ub of f is 0
    else if ( causingVar == b && causingVarBound == Tightening::UB && affectedVar == f &&
              affectedVarBound == Tightening::UB && targetBound < 0 )
    {
        matched = true;

        proofRuleRes =
            String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " ( cl " +
            getPathClause( node ) + conclusion + ") :rule resolution :premises ( resLem" +
            std::to_string( _lemmaCounter - 1 ) + " tautSplit" + std::to_string( _lemmaCounter ) +
            " split" + identifier + "_a0 split" + identifier + " split" + identifier + "_i1 ) ) \n";
    }
    // Propagate 0 ub from f to b
    else if ( causingVar == f && causingVarBound == Tightening::UB && affectedVar == b &&
              affectedVarBound == Tightening::UB && targetBound == 0 )
    {
        matched = true;
        proofRuleRes = String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " ( cl " +
                       getPathClause( node ) + conclusion +
                       ") :rule resolution :premises ( resLem" +
                       std::to_string( _lemmaCounter - 1 ) + " equiv" + identifier + "_i1) ) \n";
    }
    else if ( causingVar == b && causingVarBound == Tightening::UB && affectedVar == f &&
              affectedVarBound == Tightening::UB && targetBound == 0 )
    {
        matched = true;
        proofRuleRes = String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " ( cl " +
                       getPathClause( node ) + conclusion +
                       ") :rule resolution :premises ( resLem" +
                       std::to_string( _lemmaCounter - 1 ) + " equiv" + identifier + "_i0) ) \n";
    }
    // If ub of aux is 0, then lb of b is 0
    else if ( causingVar == aux && causingVarBound == Tightening::UB && affectedVar == b &&
              affectedVarBound == Tightening::LB && targetBound == 0 )

    {
        matched = true;
        proofRuleRes = String( "( step resLem" + std::to_string( _lemmaCounter ) ) + " ( cl " +
                       getPathClause( node ) + conclusion +
                       ") :rule resolution :premises ( resLem" +
                       std::to_string( _lemmaCounter - 1 ) + " equiv" + identifier + "_a1) ) \n";
    }

    /* TODO support all lemma types
    // If lb of b is negative x, then ub of aux is -x
    else if ( causingVar == b && causingVarBound == Tightening::LB && affectedVar == aux &&
              affectedVarBound == Tightening::UB &&
              FloatUtils::isNegative( explainedBound - epsilon ) )
        return -explainedBound;

    // If ub of b is positive, then propagate to f
    else if ( causingVar == b && causingVarBound == Tightening::UB && affectedVar == f &&
              affectedVarBound == Tightening::UB &&
              FloatUtils::isPositive( explainedBound + epsilon ) )
        return explainedBound;

    */

    Vector<Stack<std::tuple<int, double>>> &affectedTempVec =
        ( affectedVarBound == Tightening::UB ) ? _currentUpperBounds : _currentLowerBounds;
    if ( matched )
    {
        affectedTempVec[affectedVar].push( std::tuple<int, double>( _lemmaCounter, bound ) );


        _proof.append( laGeneric );
        _proof.append( res );
        _proof.append( proofRule );
        _proof.append( proofRuleRes );
        ++_lemmaCounter;
    }
    else
    {
        // Keep consistency of the stacks with the lemmas
        std::tuple<int, double> dummy =
            std::tuple<int, double>( affectedTempVec[affectedVar].top() );
        affectedTempVec[affectedVar].push( dummy );
        --_lemmaCounter;
    }
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
    if ( explainedVar >= 0 )
    {
        mpq_t temp;
        mpq_init( temp );
        mpq_set_d( temp, 1 );
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

            mpq_class temp( isUpper ? -entry._value : entry._value );
            farkasArgs += temp.get_str() + " ";
            farkasParticipants += String( "e" + std::to_string( entry._index ) ) + " ";
        }

    for ( unsigned i = 0; i < _n; ++i )
    {
        mpq_class temp( explainedRow[i] );
        if ( ( mpq_sgn( explainedRow[i] ) > 0 && isUpper ) ||
             ( mpq_sgn( explainedRow[i] ) < 0 && !isUpper ) )
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
        else if ( ( mpq_sgn( explainedRow[i] ) < 0 && isUpper ) ||
                  ( mpq_sgn( explainedRow[i] ) > 0 && !isUpper ) )
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

void AletheProofbWriter::writeDelegatedLeaf( const UnsatCertificateNode *node )
{
    String proofHole = String( "( step res" + std::to_string( _stepCounter ) ) + " (cl " +
                       getPathClause( node ) + ") :rule hole ) \n";
    _proof.append( proofHole );
}