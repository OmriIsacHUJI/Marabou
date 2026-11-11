/*********************                                                        */
/*! \file AletheProofWriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Omri Isac, Guy Katz
 ** This file is part of the Marabou project.
 ** Copyright (c) 2017-2026 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved. See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 **/

#include "AletheProofWriter.h"

AletheProofWriter::AletheProofWriter( const Map<unsigned, double> &upperBounds,
                                      const Map<unsigned, double> &lowerBounds,
                                      const GroundBoundManager &groundBoundManager,
                                      const List<Equation> &unprocessedEquations,
                                      const List<PiecewiseLinearConstraint *> &problemConstraints )
    : _initialTableau( NULL )
    , _initialUpperBounds( upperBounds )
    , _initialLowerBounds( lowerBounds )
    , _groundBoundManager( groundBoundManager )
    , _plc( problemConstraints.begin(), problemConstraints.end() )
    , _unprocessedEquations( unprocessedEquations )
    , _numOfInequalities( 0 )
    , _n( upperBounds.size() )
    , _m( 0 )
    , _varToPlc()
    , _idToSplits()
    , _nodeToSplits()
{
    // The original bound values and equations are already available here.
    // Tableau auxiliary variables are not available until initializeTableau().
    for ( const auto &eq : _unprocessedEquations )
        if ( eq._type != Equation::EQ )
            ++_numOfInequalities;

    for ( auto *plc : _plc )
    {
        if ( plc->getType() != RELU )
            continue;

        const auto *relu = static_cast<const ReluConstraint *>( plc );

        _reluBaseLowerVars.insert( relu->getF() );
    }
}

void AletheProofWriter::initializeTableau(
    unsigned explanationSize,
    const Vector<double> &upperBounds,
    const Vector<double> &lowerBounds,
    const SparseMatrix *tableau,
    const List<PiecewiseLinearConstraint *> &problemConstraints )
{
    ASSERT( upperBounds.size() == lowerBounds.size() );
    ASSERT( explanationSize <= upperBounds.size() );
    _reluBaseLowerVars.clear();
    _reluBaseUpperVars.clear();
    _initialTableau = tableau;
    _n = upperBounds.size();

    for ( unsigned i = 0; i < _n; ++ i )
    {
        if ( !_initialUpperBounds.exists( i ) )
           _addedUpperBounds.insert(i, upperBounds[i]);

        if ( !_initialLowerBounds.exists( i ) )
            _addedLowerBounds.insert(i, lowerBounds[i]);
    }

    _m = explanationSize;
    _plc = Vector<PiecewiseLinearConstraint *>(
        problemConstraints.begin(), problemConstraints.end() );

    _varToPlc.clear();
    _reluAuxVars.clear();
    for ( auto *plc : _plc )
    {
        for ( unsigned var : plc->getParticipatingVariables() )
            _varToPlc.insert( var, plc );

       if ( !plc->getTableauAuxVars().empty() )
            _varToPlc.insert( plc->getTableauAuxVars().front(), plc );

       if ( plc->getType() == RELU )
       {
            _reluAuxVars.insert( plc->getParticipatingVariables().back() );
            _reluAuxVars.insert( plc->getTableauAuxVars() );
            const ReluConstraint *relu = static_cast<const ReluConstraint *>( plc );

            _reluBaseLowerVars.insert( relu->getF() );
            _reluBaseLowerVars.insert( relu->getAux() );
            _reluBaseUpperVars.insert( relu->getAux() );
       }
    }
    // All auxiliary variables are required to write these assumptions
    writeTableauAssumptions();
}

void AletheProofWriter::writeTableauAssumptions()
{
    ASSERT( _assumptions.empty() );
    unsigned counter = 0;
    unsigned ineqCounter = _numOfInequalities;
    // Convert assertions to assumptions
    for ( const auto &eq : _unprocessedEquations )
    {
        unsigned size = 0;
        for ( const auto &addend : eq._addends )
            if ( addend._coefficient != 0 )
                ++size;

        if ( !size )
            return;
        mpq_class eqScalar( eq._scalar );
        String scalar = eqScalar.get_str();

        if ( eqScalar.get_den() == 1 )
            scalar += ".0";

        String stepPrefix = eq._type == Equation::EQ ? "e" : "pre";

        String eqLine = String("(assume ") + stepPrefix + std::to_string( counter ) + "(!";

        if ( eq._type == Equation::EQ )
            eqLine += "(= ";
        else if ( eq._type == Equation::LE )
            // Scalar should be >= than sum of addends
            eqLine += "(>= ";
        else
            // Scalar should be <= than sum of addends
            eqLine += "(<= ";

        eqLine += String( "(! " ) + scalar + " :named x" + std::to_string( _n - _m + counter ) + ")";

        if ( size > 1 )
            eqLine += String( "(+" );

        eqLine += SmtLibWriter::writeEqAddends( eq._addends );

        if ( size > 1 )
            eqLine += String( ")" );

        eqLine += String( "):named " ) + stepPrefix + std::to_string( counter ) + "))\n";

        _assumptions.append( eqLine );

        if ( eq._type != Equation::EQ )
        {
            proveEqualityWithSlackFromInequality( eq, counter, _n - _m - _plc.size() - ineqCounter );
            --ineqCounter;
        }
        ++counter;
    }
}

void AletheProofWriter::proveEqualityWithSlackFromInequality( Equation eq, unsigned eqIndex, unsigned auxIndex )
{
    ASSERT( eq._type != Equation::EQ );

    const bool isLE = eq._type == Equation::LE;

    const String index = std::to_string( eqIndex );
    const String auxIndexStr = std::to_string( auxIndex );
    const String aux = String( "x" ) + auxIndexStr;
    const String pre = String( "pre" ) + index;
    const String slack = String( "slk" ) + index;

    // LE: lower bound; GE: upper bound.
    const String boundName = String( isLE ? "base_l" : "base_u" ) + auxIndexStr;

    // Original left-hand side.
    const String lhs = String( "(+" ) + SmtLibWriter::writeEqAddends( eq._addends ) + ")";

    mpq_class scalarValue( eq._scalar );
    String scalar = scalarValue.get_str();

    if ( scalarValue.get_den() == 1 )
        scalar += ".0";

    // normalized = lhs - scalar
    String normalized;

    if ( scalarValue != 0 )
        normalized = String( "(+ " ) + lhs + " (- " + scalar + "))";
    else
        normalized = lhs;

    // x_aux := -normalized = scalar - lhs
    const String slackDefinition =
            String( "(! (- " ) + normalized + "):named " + aux + ")";

    const String equalityLhs = String( "(+ " ) + normalized + " " + aux + ")";

    const String equality = String( "(= 0.0 " ) + equalityLhs + ")";

    const String le = String( "(<= " ) + equalityLhs + " 0.0)";

    const String ge = String( "(<= 0.0 " ) + equalityLhs + ")";

    // LE: x_aux >= 0
    // GE: x_aux <= 0
    const String boundWithDefinition = String( isLE ? "(>= " : "(<= " ) + slackDefinition + " 0.0)";

    const String bound = String( isLE ? "(>= " : "(<= " ) + aux + " 0.0)";

    String proof;

    // Derive the appropriate slack bound from pre<eqIndex>.
    proof += String( "(step " ) + slack + "_imp (cl (not " + pre + ") " + boundWithDefinition + ")"
                                   ":rule la_generic :args (1 1))\n";

    // LE: l<auxIndex>
    // GE: u<auxIndex>
    proof += String( "(step " ) + boundName + " (cl (!" + bound + " :named " + boundName +
             ")):rule resolution :premises (" + slack + "_imp " + pre + "))\n";

    // The following steps are unchanged for LE and GE.
    // Because x_aux = -normalized,
    // equalityLhs is identically zero.
    proof += String( "(step " ) + slack + "_le (cl " + le + "):rule la_generic :args (1))\n";

    proof += String( "(step " ) + slack + "_ge (cl " + ge + "):rule la_generic :args (1))\n";

    // la_disequality produces a single disjunction.
    proof += String( "(step " ) + slack + "_dis (cl (or " + equality + " (not " + ge + ")" +
             " (not " + le + "))):rule la_disequality)\n";

    // Flatten the disjunction.
    proof += String( "(step " ) + slack + "_or (cl " + equality + " (not " + ge + ")" +
             " (not " + le + ")):rule or :premises (" + slack + "_dis))\n";

    // Derive the equality.
    proof += String( "(step e" ) + index +" (cl (!" + equality + " :named e" + index +
             ")):rule resolution :premises (" + slack + "_or " + slack + "_ge " + slack + "_le))\n";

    _plcSteps.append( proof );
}

void AletheProofWriter::writeBoundAssumptions()
{
    for ( const auto &entry : _initialUpperBounds )
    {
        if ( _reluBaseUpperVars.exists( entry.first ) || entry.second == std::numeric_limits<double>::max() )
            continue;

        const String var = std::to_string( entry.first );
        const mpq_class bound( entry.second );
        const String value = bound.get_den() == 1 ? bound.get_str() + ".0" : bound.get_str();

        _assumptions.append( String( "(assume input_u" ) + var +" (!(<= x" + var + " " + value +
                                "):named input_u" + var + "))\n" );
    }

    for ( const auto &entry : _initialLowerBounds )
    {
        if ( _reluBaseLowerVars.exists( entry.first ) || entry.second == -std::numeric_limits<double>::max() )
            continue;

        const String var = std::to_string( entry.first );
        const mpq_class bound( entry.second );

        const String value = bound.get_den() == 1 ? bound.get_str() + ".0" : bound.get_str();

        _assumptions.append( String( "(assume input_l" ) + var + " (!(>= x" + var + " " + value +
                                    "):named input_l" + var + "))\n" );
    }
}

void AletheProofWriter::writePLCAssumption()
{
    List<String> plcAssumptions = List<String>();
    List<String> plcSplits = List<String>();

    for ( const auto &plc : _plc )
    {
        List<PiecewiseLinearCaseSplit> splitsInFixedOrder = {};
        // TODO support additional types
        int constraintInt = plc->getTableauAuxVars().front();

        String constraintNum = std::to_string( constraintInt );
        String plcAssumption = "";

        if ( plc->getType() == RELU )
        {
            splitsInFixedOrder.append( { plc->getCaseSplit( RELU_PHASE_ACTIVE ),
                                         plc->getCaseSplit( RELU_PHASE_INACTIVE ) } );

            ReluConstraint *relu = ( ReluConstraint * )plc;
            String f = std::to_string( relu->getF() );
            String b = std::to_string( relu->getB() );
            String aux = std::to_string( relu->getAux() );

            // Use common SMT representation
            String bEqualsF = String( "(= x" ) + b + " x" + f + ")";

            plcAssumption += String( "(assume relu" ) + constraintNum + " (ite (!(<= 0.0 x" + b +
                             "):named a" + constraintNum + ")" + bEqualsF + "(<= x" + f +
                             " 0.0)))\n";
            plcAssumption += String( "(assume base_l" ) + f + " (!(>= x" + f + " 0.0):named base_l" + f + "))\n";
            plcAssumptions.append( plcAssumption );

            // Eagerly write basic ite resolution steps used in lemmas
            String ite1 = String( "(step ri1_" ) + constraintNum + " (cl (<= 0.0 x" + b + ")(<= x" +
                          f + " 0.0)):rule ite1 :premises(relu" + constraintNum + "))\n";
            String ite2 = String( "(step ri2_" ) + constraintNum + " (cl (not (<= 0.0 x" + b +
                          "))" + bEqualsF + "):rule ite2 :premises(relu" + constraintNum + "))\n";
            String tot = String( "(step _bt" ) + constraintNum + " (cl (or (<= x" + b +
                         " 0.0)(<= 0.0 x" + b + "))):rule la_totality)\n";
            tot += String( "(step bt" ) + constraintNum + " (cl (<= x" + b + " 0.0)(<= 0.0 x" + b +
                   ")):rule or :premises(_bt" + constraintNum + "))\n";
            _plcSteps.append( { ite1, ite2, tot } );

            // Write the lower bound of aux variable, and name it as its aux variable
            String auxLowerBound = String( "(step auxlb1_" ) + constraintNum +
                    " (cl (not (= x" + b + " x" + f + "))" +
                    "(>= (- x" + f + " x" + b + ") 0.0 )):rule la_generic :args(-1 1))\n";
            auxLowerBound += String( "(step auxlb2_" ) + constraintNum +
                    " (cl (<= 0.0 x" + b + ")(not base_l" + f +")(>= (- x" +
                    f + " x" + b + ") 0.0)):rule la_generic :args(1 -1 1))\n";
            mpq_class auxLbMpq(_initialLowerBounds[relu->getAux()] );
            auxLowerBound += String( "(step base_l" ) + aux + " (cl (>= (!(- x" + f + " x" + b + "):named x" + aux
                    + ") 0.0)):rule resolution :premises(ri2_" + constraintNum + " auxlb1_" + constraintNum + " auxlb2_"
                    + constraintNum + " base_l" + f + "))\n";

            _plcSteps.append( { auxLowerBound } );

            unsigned identifierInt = relu->getTableauAuxVars().front();
            String tableauEq = "e" + std::to_string( identifierInt - ( _n - _m ) );
            String tableauLit = convertTableauAssumptionToClause( identifierInt - ( _n - _m ) );
            String tableauEqTmp = tableauEq + "tmp";

            // Infer the relu equation
            String reluEq = String("(step pr" ) + tableauEq + "_1 (cl (<= (!(+ x" + b + " (- x" + f +") x" + aux
                    + "):named " + tableauEqTmp + ") 0.0)):rule la_generic :args(1))\n";
            reluEq += String("(step pr" ) + tableauEq + "_2 (cl (<= 0.0 " + tableauEqTmp + ")):rule la_generic :args(1))\n";
            reluEq += String("(step pr" ) + tableauEq + "_3 (cl (or (!(= "+ tableauEqTmp + " 0.0):named " + tableauEq +
                    ") (not (<= " + tableauEqTmp + " 0.0))" + "(not (<= 0.0 " + tableauEqTmp + ")))):rule la_disequality)\n";
            reluEq += String("(step pr" ) + tableauEq + " (cl (= "+ tableauEqTmp + " 0.0)(not (<= " + tableauEqTmp + " 0.0))" + "(not (<= 0.0 " + tableauEqTmp + "))):rule or :premises (pr" + tableauEq +"_3))\n";
            reluEq += String("(step " ) + tableauEq + " (cl " + tableauEq +"):rule resolution :premises(pr"+ tableauEq + " pr"+ tableauEq +"_1 pr"+ tableauEq + "_2))\n";
            _plcSteps.append( reluEq );

            // Eagerly write basic bound resolution steps used in lemmas
            // Clauses used to derive one split bound from the other (for both ReLU possible phases)
            String activeBound1 = String( "(step ab1_" ) + constraintNum + " (cl (not " + bEqualsF +
                                  ")" + tableauLit + "(<= x" + aux + " 0.0)):rule la_generic :args(1 -1 1))\n";
            activeBound1 += String( "(step eq" ) + constraintNum + "_a0" + " (cl (not (<= 0.0 x" +
                            b + "))(<= x" + aux + " 0.0)):rule resolution :premises(ab1_" +
                            constraintNum + " ri2_" + constraintNum + " " +
                            tableauEq + "))\n";

            String inactiveBound1 = String( "(step ib1_" ) + constraintNum + " (cl (not " +
                                    bEqualsF + ")(not(<= x" + b + " 0.0))(<= x" + f +
                                    " 0.0)):rule la_generic :args(1 1 1))\n";
            inactiveBound1 += String( "(step eq" ) + constraintNum + "_i0" + " (cl (not (<= x" + b +
                              " 0.0))(<= x" + f + " 0.0)):rule resolution :premises(ib1_" +
                              constraintNum + " ri1_" + constraintNum + " ri2_" + constraintNum +
                              "))\n";

            String inactiveBound2 = String( "(step ib2_" ) + constraintNum + " (cl (not " +
                                    bEqualsF + ")(<= x" + b + " 0.0)(not (<= x" + f +
                                    " 0.0))):rule la_generic :args(-1 1 1))\n";
            inactiveBound2 += String( "(step eq" ) + constraintNum + "_i1" + " (cl (not (<= x" + f +
                              " 0.0))(<= x" + b + " 0.0)):rule resolution :premises(ib2_" +
                              constraintNum + " ri2_" + constraintNum + " bt" + constraintNum +
                              "))\n";
            _plcSteps.append( { activeBound1, inactiveBound1, inactiveBound2 } );

            if ( plc->phaseFixed() )
                continue;

            String activeBound2 = String( "(step ab2_" ) + constraintNum + " (cl (<= 0.0 x" + b +
                                  ")" + tableauLit + "(not (<= x" + aux + " 0.0))(not (>= x" + f +
                                  " 0.0))):rule la_generic :args(1 1 1 -1))\n";
            activeBound2 += String( "(step eq" ) + constraintNum + "_a1" + " (cl (<= 0.0 x" + b +
                            ")(not (<= x" + aux + " 0.0))):rule resolution :premises(ab2_" +
                            constraintNum + " " + tableauEq + " base_l" + f + "))\n";

            _plcSteps.append(  activeBound2 );
        }
    }

    _assumptions.append( plcAssumptions );
    _assumptions.append( plcSplits );
}

void AletheProofWriter::writeContradiction( const SparseUnsortedList &contradiction,
                                            UnsatCertificateNode *node )
{
    String farkasArgs = "";
    String farkasClause = "";
    String farkasParticipants = "";
    String negatedSplitsClause = "";
    unsigned nodeId = node->getId();

    // Collect all Farkas lemma information
    farkasStrings( contradiction,
                   _groundBoundManager.getCounter(),
                   farkasArgs,
                   farkasClause,
                   farkasParticipants,
                   negatedSplitsClause,
                   nodeId == 0 ? -1 : -(int)nodeId,
                   true,
                   node );

    farkasClause = String( "(cl " ) + farkasClause + ")";
    farkasArgs = String( "(" ) + farkasArgs + "))\n";

    // Write la_generic\bounded_farkas rule, followed by the corresponding resolution
    String ruleName = GlobalConfiguration::DEDICATED_ALETHE_RULE ? "bounded_farkas" : "la_generic";
    String laGeneric = String( "(step t" + std::to_string( nodeId ) ) + " " + farkasClause +
                       ":rule " + ruleName + " :args" + farkasArgs;

    String res = String( "(step r" + std::to_string( nodeId ) ) + " (cl " + negatedSplitsClause +
                 "):rule resolution :premises(t" + std::to_string( nodeId ) + " " +
                 farkasParticipants + "))\n";

    _proof.append( { laGeneric, res } );
}

void AletheProofWriter::writeInstanceToFile( IFile &file )
{
    file.open( File::MODE_WRITE_TRUNCATE );

    // Gather and write all assumptions
    writeBoundAssumptions();
    writePLCAssumption();

    for ( const String &s : _assumptions )
        file.write( s );

    // ReLU and slack-variable foundational steps.
    for ( const String &s : _plcSteps )
        file.write( s );

    // Bounds derived during preprocessing.
    for ( const String &s : _preprocessSteps )
        file.write( s );

    // Final canonical bounds used during solving.
    writeFinalPreprocessingBounds();

    for ( const String &s : _finalBoundSteps )
        file.write( s );

    for ( const String &s : _proof )
        file.write( s );

    file.close();
}

void AletheProofWriter::writeChildrenConclusion( const UnsatCertificateNode *node )
{
    if ( !node->isValidNonLeaf() )
        return;

    // Collect children information
    List<unsigned> childrenIndices = {};
    for ( const auto &child : node->getChildren() )
        childrenIndices.append( child->getId() );

    ASSERT( node->isValidNonLeaf() );
    ASSERT( childrenIndices.size() == 2 );
    PiecewiseLinearCaseSplit firstChildSplit = node->getChildren().front()->getSplit();
    PiecewiseLinearCaseSplit secondChildSplit = node->getChildren().back()->getSplit();

    List<Tightening> tighteningDeps = _nodeToSplits[node->getChildren().front()->getId()];
    tighteningDeps.append( _nodeToSplits[node->getChildren().back()->getId()] );
    List<Tightening> filteredTighteneings = {};
    Set<int> phaseIdentifiers = {};
    List<PiecewiseLinearCaseSplit> splitDeps = {};

    // Detect which child corresponds to which phase
    for ( const auto &tightening : tighteningDeps )
    {
        if ( firstChildSplit.getBoundTightenings().exists( tightening ) ||
             secondChildSplit.getBoundTightenings().exists( tightening ) )
            continue;

        PiecewiseLinearConstraint *plc = _varToPlc[tightening._variable];

        for ( const auto &caseSplit : plc->getAllCases() )
        {
            PiecewiseLinearCaseSplit split = plc->getCaseSplit( caseSplit );
            if ( split.getBoundTightenings().exists( tightening ) )
                phaseIdentifiers.insert( isSplitActive( split )
                                             ? (int)plc->getTableauAuxVars().front()
                                             : -(int)plc->getTableauAuxVars().front() );
        }
    }

    // Collect the underlying clause from the splits used in the derivation (subset of the node's
    // path)
    for ( const auto phase : phaseIdentifiers )
    {
        if ( !phaseIdentifiers.exists( -phase ) )
        {
            PiecewiseLinearCaseSplit splitToAdd;
            PiecewiseLinearConstraint *plc = _varToPlc[abs( phase )];

            // TODO support additional types of splits
            if ( plc->getType() == RELU )
                splitToAdd = phase > 0 ? plc->getCaseSplit( RELU_PHASE_ACTIVE )
                                       : plc->getCaseSplit( RELU_PHASE_INACTIVE );

            splitDeps.append( splitToAdd );
            filteredTighteneings.append( splitToAdd.getBoundTightenings().front() );
        }
    }

    _nodeToSplits.insert( node->getId(), filteredTighteneings );

    ASSERT( node->isValidNonLeaf() );
    ASSERT( childrenIndices.size() == 2 )

    // Write resolution
    String resLine = String( "(step r" + std::to_string( node->getId() ) + " (cl " ) +
                     getNegatedSplitsClause( splitDeps ) + "):rule resolution :premises(r" +
                     std::to_string( childrenIndices.front() ) + " r" +
                     std::to_string( childrenIndices.back() ) + "))\n";

    _proof.append( resLine );
}

String
AletheProofWriter::getNegatedSplitsClause( const List<PiecewiseLinearCaseSplit> &splits ) const
{
    if ( splits.empty() )
        return "";

    String clause = "";
    for ( const auto &split : splits )
    {
        String isActive = isSplitActive( split ) ? "(not a" : "a";
        PiecewiseLinearConstraint *plc = _varToPlc[split.getBoundTightenings().front()._variable];
        int constraintInt = plc->getTableauAuxVars().front();
        String plcNum = std::to_string( constraintInt );
        String suffix = isSplitActive( split ) ? ")" : "";
        clause += String( " " ) + isActive + plcNum + suffix;
    }
    return clause;
}

String AletheProofWriter::getBoundAsClause( const Tightening &bound ) const
{
    mpq_class boundMpq(bound._value);

    String boundStr = boundMpq.get_den().get_str() == "1"
                      ? boundMpq.get_str() + ".0"
                      : boundMpq.get_str();

    if ( bound._type == Tightening::UB )
        return String( "(<= x" + std::to_string( bound._variable ) + " " ) +
                boundStr + ")";

    return String( "(>= x" + std::to_string( bound._variable ) + " " ) +
            boundStr + ")";
}

bool AletheProofWriter::isSplitActive( const PiecewiseLinearCaseSplit &split ) const
{
    ASSERT( split.getEquations().empty() )
    return split.getBoundTightenings().back()._type == Tightening::LB ||
           split.getBoundTightenings().front()._type == Tightening::LB;
}

List<PiecewiseLinearCaseSplit>
AletheProofWriter::getPathSplits( const UnsatCertificateNode *node ) const
{
    List<PiecewiseLinearCaseSplit> pathSplits = List<PiecewiseLinearCaseSplit>();
    const UnsatCertificateNode *cur = node;
    while ( cur && !cur->getSplit().getBoundTightenings().empty() )
    {
        pathSplits.append( cur->getSplit() );
        cur = cur->getParent();
    }

    return pathSplits;
}

void AletheProofWriter::writeLemma(
    const std::shared_ptr<GroundBoundManager::GroundBoundEntry> &lemmaEntry )
{
    if ( !lemmaEntry->lemma || !lemmaEntry->lemma->getToCheck() )
        return;

    PiecewiseLinearConstraint *matchedConstraint = _varToPlc[lemmaEntry->lemma->getAffectedVar()];

    // TODO add support for all types of PLCs
    if ( matchedConstraint && matchedConstraint->getType() == RELU )
        writeReluLemma( lemmaEntry, (ReluConstraint *)matchedConstraint );
}

void AletheProofWriter::writeReluLemma(
    const std::shared_ptr<GroundBoundManager::GroundBoundEntry> &lemmaEntry,
    const ReluConstraint *relu,
    bool preprocessing )
{
    ASSERT( lemmaEntry->lemma && lemmaEntry->lemma->getConstraintType() == RELU );

    // Collect lemma and Relu information
    const std::shared_ptr<PLCLemma> lemma = lemmaEntry->lemma;

    unsigned causingVar = lemma->getCausingVars().front();
    unsigned affectedVar = lemma->getAffectedVar();
    double targetBound = lemma->getMinTargetBound();
    double bound = lemma->getBound();
    String id = preprocessing ? String( "pp_" ) + std::to_string( _nextPreprocessingBoundId++ )
                              : std::to_string( lemma->getId() );

    const List<SparseUnsortedList> &explanations = lemma->getExplanations();
    Tightening::BoundType causingVarBound = lemma->getCausingVarBound();
    Tightening::BoundType affectedVarBound = lemma->getAffectedVarBound();

    if ( !preprocessing )
        ASSERT( relu == _varToPlc[affectedVar] );
    ASSERT( explanations.size() == 1 );

    String farkasArgs = "";
    String farkasClause = "";
    String farkasParticipants = "";
    String negatedSplitClause = "";
    String causeBound = getBoundAsClause( Tightening( causingVar, targetBound, causingVarBound ) );

    if ( causingVar == relu->getB() && causingVarBound == Tightening::LB && affectedVar == relu->getAux() &&
          affectedVarBound == Tightening::UB && targetBound == 0 )
        // Match the literal used by eq<id>_a0.
        // (>= x 0.0) and (<= 0.0 x) are equivalent
        // arithmetically, but not identical resolution pivots.
        causeBound = String( "(<= 0.0 x" ) +
                     std::to_string( causingVar ) + ")";

    String laGeneric = "";
    String res = "";
    if ( !preprocessing )
    {
        // Apply calculations of the Farkas lemma, to prove the causing bound
        farkasStrings( explanations.front(),
                       lemmaEntry->id,
                       farkasArgs,
                       farkasClause,
                       farkasParticipants,
                       negatedSplitClause,
                       causingVar,
                       causingVarBound == Tightening::UB,
                       NULL );

        farkasClause = String( "(cl " ) + causeBound + farkasClause + ")";
        farkasArgs = String( "(" ) + farkasArgs + "))\n";

        // Write la_generic\bounded_farkas for proving the causing bound, followed by a resolution step
        String ruleName = GlobalConfiguration::DEDICATED_ALETHE_RULE ? "bounded_farkas" : "la_generic";
        laGeneric = String( "(step fl" ) + id + " " + farkasClause + ":rule " + ruleName +
                           " :args" + farkasArgs;

        res = String( "(step cr" ) + id + " (cl " + negatedSplitClause + causeBound +
                     "):rule resolution :premises(fl" + id + " " + farkasParticipants + "))\n";
    }

    // Collect information for proving the derivation rule from the lemma (derive the derived bound,
    // based on the causing bound)
    unsigned b = relu->getB();
    unsigned f = relu->getF();
    unsigned aux = relu->getAux();
    int constraintInt = relu->getTableauAuxVars().front();

    String identifier = std::to_string( constraintInt );
    bool matched = false;

    String proofRule = "";
    String proofRuleRes = "";
    String tempString = "";

    // Additional steps required in some cases, for deriving a phase from a tighter bound
    if ( targetBound > 0 )
        tempString += String( "(not " ) +
                      getBoundAsClause( Tightening( causingVar, 0, Tightening::UB ) ) + ")(not " +
                      causeBound + ")";
    else
        tempString += String( "(not" ) + causeBound + ")" +
                      getBoundAsClause( Tightening(
                          causingVar, 0, targetBound > 0 ? Tightening::LB : Tightening::UB ) );

    if ( targetBound != 0 )
    {
        proofRule =
            String( "(step taut" ) + id + " (cl (or " + tempString + ")):rule la_tautology)\n";
        proofRule += String( "(step ts" ) + id + " (cl " + tempString + "):rule or :premises(taut" +
                     id + "))\n";
    }

    if ( targetBound > 0 && causingVar == b )
    {
        tempString = getBoundAsClause( Tightening( causingVar, 0, Tightening::UB ) ) +
                     " (<= 0.0 x" + std::to_string( b ) + ")";

        proofRule +=
            String( "(step tot" ) + id + " (cl (or " + tempString + ")):rule la_totality)\n";
        proofRule += String( "(step tos" ) + id + " (cl " + tempString + "):rule or :premises(tot" +
                     id + "))\n";
    }

    String conclusion = getBoundAsClause( Tightening( affectedVar, bound, affectedVarBound ) );


    String causingPremise = preprocessing ? preprocessingBoundPremise( causingVar, causingVarBound )
                                          : String( "cr" ) + id;

    // Prepare the shared prefix, and conclude with the remaining rules based on the exact
    // derivation type
    String pref = String( "(step rl" ) + id + " (cl " + negatedSplitClause + conclusion +
                  "):rule resolution :premises(" + causingPremise;
    // if the lb of b or f is positive, then ub of aux is zero
    if ( ( causingVar == f || causingVar == b ) && causingVarBound == Tightening::LB &&
         affectedVar == aux && affectedVarBound == Tightening::UB && targetBound > 0 )
    {
        matched = true;
        proofRuleRes = pref + " ts" + id;

        if ( causingVar == b )
            proofRuleRes += String( " eq" ) + identifier + "_a0 tos" + id;
        else
            proofRuleRes += String( " eq" ) + identifier + "_a0 ri1_" + identifier;

        proofRuleRes += "))\n";
    }
    // if the lb of b  is zero, then so is the ub of aux
    else if ( causingVar == b && causingVarBound == Tightening::LB && affectedVar == aux &&
              affectedVarBound == Tightening::UB && targetBound == 0 )
    {
        matched = true;
        proofRuleRes = pref + " eq" + identifier + "_a0))\n";
    }
    // If lb of aux is positive, then ub of f is 0
    else if ( causingVar == aux && causingVarBound == Tightening::LB && affectedVar == f &&
              affectedVarBound == Tightening::UB && targetBound > 0 )
    {
        matched = true;
        proofRuleRes = pref + " ts" + id + " eq" + identifier + "_a0 ri1_" + identifier + "))\n";
    }

    // If ub of b is non positive, then ub of f is 0
    else if ( causingVar == b && causingVarBound == Tightening::UB && affectedVar == f &&
              affectedVarBound == Tightening::UB && targetBound < 0 )
    {
        matched = true;
        proofRuleRes = pref + " ts" + id + " eq" + identifier + "_i0))\n";
    }
    // Propagate 0 ub from f to b ...
    else if ( causingVar == f && causingVarBound == Tightening::UB && affectedVar == b &&
              affectedVarBound == Tightening::UB && targetBound == 0 )
    {
        matched = true;
        proofRuleRes = pref + " eq" + identifier + "_i1))\n";
    }
    // ... and vise versa
    else if ( causingVar == b && causingVarBound == Tightening::UB && affectedVar == f &&
              affectedVarBound == Tightening::UB && targetBound == 0 )
    {
        matched = true;
        proofRuleRes = pref + +" eq" + identifier + "_i0))\n";
    }
    // If ub of aux is 0, then lb of b is 0
    else if ( causingVar == aux && causingVarBound == Tightening::UB && affectedVar == b &&
              affectedVarBound == Tightening::LB && targetBound == 0 )

    {
        matched = true;
        proofRuleRes = pref + " eq" + identifier + "_a1))\n";
    }
    // If lb of b is negative x, then ub of aux is -x
    else if ( causingVar == b && causingVarBound == Tightening::LB && affectedVar == aux &&
              affectedVarBound == Tightening::UB && targetBound < 0 )
    {
        matched = true;

        unsigned identifierInt = relu->getTableauAuxVars().front();
        String tautClause = String( "(not " ) +
                            getBoundAsClause( Tightening( affectedVar, 0, Tightening::UB ) ) + ")" +
                            conclusion;
        proofRule =
            String( "(step taut" ) + id + " (cl (or " + tautClause + ")):rule la_tautology)\n";

        proofRule += String( "(step ts" ) + id + " (cl " + tautClause + "):rule or :premises(taut" +
                     id + "))\n";

        String subConclusion = getBoundAsClause( Tightening( f, 0, Tightening::UB ) );
        String tableauLit = convertTableauAssumptionToClause( identifierInt - ( _n - _m ) );
        String subFarkasClause = String( " (cl (not " ) + causeBound + ")" + conclusion + "(not " +
                                 subConclusion + ")" + tableauLit;

        proofRule += String( "(step ifl" ) + id + subFarkasClause +
                     "):rule la_generic :args(1 1 -1 -1))\n";

        proofRuleRes += pref + +" e" + std::to_string( identifierInt - ( _n - _m ) ) + " ifl" + id + " ts" + id + " eq" +
                        identifier + "_a0 ri1_" + identifier + "))\n";
    }
    // If ub of b is positive, then propagate to f
    else if ( causingVar == b && causingVarBound == Tightening::UB && affectedVar == f &&
              affectedVarBound == Tightening::UB && targetBound > 0 )
    {
        matched = true;

        unsigned identifierInt = relu->getTableauAuxVars().front();
        String tautClause = String( "(not " ) +
                            getBoundAsClause( Tightening( affectedVar, 0, Tightening::UB ) ) + ")" +
                            conclusion;

        proofRule =
            String( "(step taut" ) + id + " (cl (or " + tautClause + ")):rule la_tautology)\n";

        proofRule += String( "(step ts" ) + id + " (cl " + tautClause + "):rule or :premises(taut" +
                     id + "))\n";


        String subConclusion = getBoundAsClause( Tightening( aux, 0, Tightening::UB ) );
        String tableauLit = convertTableauAssumptionToClause( identifierInt - ( _n - _m ) );
        String subFarkasClause = String( " (cl (not " ) + causeBound + ")" + conclusion + "(not " +
                                 subConclusion + ")" + tableauLit;

        proofRule +=
            String( "(step ifl" ) + id + subFarkasClause + "):rule la_generic :args(1 1 -1 1))\n";

        proofRuleRes += pref + " e" + std::to_string( identifierInt - ( _n - _m ) ) + " ifl" + id + " ts" + id + " eq" +
                        identifier + "_a0 ri1_" + identifier + "))\n";
    }

    if ( matched )
    {
        if ( preprocessing )
        {
            _preprocessSteps.append( { proofRule, proofRuleRes } );

            const Tightening result( affectedVar, bound, affectedVarBound );
            updatePreprocessingBound( result );
            setPreprocessingBoundPremise( result, String( "rl" ) + id );
        }
        else
            _proof.append( { laGeneric, res, proofRule, proofRuleRes } );
    }
}

void AletheProofWriter::linearCombinationMpq( const std::vector<mpq_t> &explainedRow,
                                              const SparseUnsortedList &expl ) const
{
    SparseUnsortedList tableauRow( _n );
    for ( const auto &entry : expl )
    {
        if ( entry._value == 0 )
            continue;

        _initialTableau->getRow( entry._index, &tableauRow );
        for ( const auto &tableauEntry : tableauRow )
        {
            // Add ci * xi to the explained row in the ith index
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

void AletheProofWriter::farkasStrings( const SparseUnsortedList &expl,
                                       unsigned entryId,
                                       String &farkasArgs,
                                       String &farkasClause,
                                       String &farkasParticipants,
                                       String &negatedSplitClause,
                                       int explainedVar,
                                       bool isUpper,
                                       UnsatCertificateNode *node )
{
    std::vector<mpq_t> explainedRow = std::vector<mpq_t>( _n );
    for ( const auto num : explainedRow )
        mpq_init( num );

    linearCombinationMpq( explainedRow, expl );
    bool isLemma = explainedVar >= 0;
    if ( isLemma )
    {
        mpq_class lemmaMultiplier( 1 );
        mpq_add(
                explainedRow[explainedVar],
                explainedRow[explainedVar],
                lemmaMultiplier.get_mpq_t() );
    }

    farkasClause = "";
    farkasArgs = "";
    farkasParticipants = "";
    List<Tightening> splitDeps;

    if ( isLemma )
        farkasArgs += "1 ";

    unsigned nWithoutTableauAuxVars = _n - _m;
    // Deduce the participating equations and their Farkas coefficients
    for ( const auto entry : expl )
        if ( entry._value != 0 )
        {
            farkasClause += String( "(not e" + std::to_string( entry._index ) ) + ")";

            mpq_class temp( isUpper ? -entry._value : entry._value );
            farkasArgs += temp.get_str() + " ";
            farkasParticipants += String( "e" + std::to_string( entry._index ) ) + " ";
        }

    for ( unsigned i = 0; i < nWithoutTableauAuxVars; ++i )
    {
        // Deduce the participating bounds, either derived from lemmas, splits, or from the input
        mpq_class temp( explainedRow[i] );
        if ( mpq_sgn( explainedRow[i] ) == 0 )
            continue;

        bool useEntryUpperBound = ( mpq_sgn( explainedRow[i] ) > 0 && isUpper ) ||
                                  ( mpq_sgn( explainedRow[i] ) < 0 && !isUpper );

        String boundString = useEntryUpperBound ? "u" : "l";
        Tightening::BoundType boundType = useEntryUpperBound ? Tightening::UB : Tightening::LB;
        const std::shared_ptr<GroundBoundManager::GroundBoundEntry> &gbEntry =
            _groundBoundManager.getGroundBoundEntryUpToId( i, boundType, entryId );

        int lemId = gbEntry->lemma ? gbEntry->lemma->getId() : -1;
        mpq_class boundMpq(gbEntry->val);
        String boundStr = boundMpq.get_den().get_str() == "1"
                          ? boundMpq.get_str() + ".0"
                          : boundMpq.get_str();

        bool isLemmaIncluded = lemId >= 0 && gbEntry->lemma->getToCheck();
        bool useSplitBound = ( lemId < 0 && gbEntry->isPhaseFixing );

        String ineqString;

        // Add the bound itself to the clause
        if ( useEntryUpperBound )
            ineqString = String( "(not (<= x" + std::to_string( i ) + " " ) +
                    boundStr + ")) ";
        else
            ineqString = String( "(not (<= " ) + boundStr + " x" +
                         std::to_string( i ) + ")) ";

        // Add the bound coefficient only if the generic rule is used
        if ( !GlobalConfiguration::DEDICATED_ALETHE_RULE )
            farkasArgs += temp.get_str() + " ";

        // Use the bound if it is learned by a lemma, or by a split
        if ( isLemmaIncluded || useSplitBound )
            farkasClause += ineqString;
        // If an input bound is used, then add it by its name
        else
        {
            farkasClause += String( "(not " ) + boundString + std::to_string( i ) + ") ";
            farkasParticipants += boundString + std::to_string( i ) + " ";
        }

        // Add split deps of previous lemmas
        if ( isLemmaIncluded )
        {
            farkasParticipants += String( "rl" + std::to_string( lemId ) ) + " ";
            for ( const auto dep : _idToSplits[gbEntry->id] )
                if ( !splitDeps.exists( dep ) )
                    splitDeps.append( dep );
        }
        // Add split deps of previous splits
        else if ( useSplitBound )
        {
            splitDeps.append( Tightening( i, gbEntry->val, boundType ) );

            String identifier = std::to_string( _varToPlc[i]->getTableauAuxVars().front() );
            if ( ( i == _varToPlc[i]->getParticipatingVariables().front() && boundMpq == 0.0 &&
                   boundType == Tightening::UB ) )
                farkasParticipants += String( "eq" ) + identifier + "_i1 ";

            if ( !( i == _varToPlc[i]->getParticipatingVariables().front() && boundMpq == 0.0 &&
                    boundType == Tightening::LB ) )
            {
                if ( i == _varToPlc[i]->getParticipatingVariables().back() )
                    farkasParticipants += String( "eq" ) + identifier + "_a0 ";
                else
                    farkasParticipants += String( "ri1_" ) + identifier + " ";
            }
        }
    }

    for ( const auto num : explainedRow )
        mpq_clear( num );

    // Add proof terms for all splits in node path, with 0 argument for those that are not
    // actually used Enables elaboration in Carcara
    if ( node && GlobalConfiguration::ALETHE_ELABORATE_TERMS )
    {
        List<PiecewiseLinearCaseSplit> nodePath = getPathSplits( node );
        for ( const auto &caseSplit : nodePath )
        {
            bool isCaseIncluded = false;
            for ( const auto &bound : caseSplit.getBoundTightenings() )
                if ( splitDeps.exists( bound ) )
                    isCaseIncluded = true;

            if ( isCaseIncluded )
                continue;

            farkasArgs += "0 ";
            String identifier =
                std::to_string( _varToPlc[caseSplit.getBoundTightenings().front()._variable]
                                    ->getTableauAuxVars()
                                    .front() );
            farkasClause += isSplitActive( caseSplit ) ? String( " (not a" ) + identifier + ")"
                                                       : String( " a" ) + identifier;
            splitDeps.append( caseSplit.getBoundTightenings().front() );
        }
    }

    if ( isLemma && _idToSplits.exists( entryId ) )
        _idToSplits[entryId] = splitDeps;
    else if ( isLemma )
        _idToSplits.insert( entryId, splitDeps );
    else
        _nodeToSplits.insert( -explainedVar, splitDeps );

    // Compute the learned activation pattern from the bounds, and write its negation as a clause
    Set<unsigned> usedPlc = {};
    for ( const auto &tightening : splitDeps )
    {
        PiecewiseLinearConstraint *plc = _varToPlc[tightening._variable];

        // Avoid repetitions
        if ( usedPlc.exists( plc->getTableauAuxVars().front() ) )
            continue;

        usedPlc.insert( plc->getTableauAuxVars().front() );
        String identifier = std::to_string( plc->getTableauAuxVars().front() );

        PiecewiseLinearCaseSplit tighteningSplit;

        for ( const auto &casSplit : plc->getAllCases() )
        {
            PiecewiseLinearCaseSplit split = plc->getCaseSplit( casSplit );
            if ( split.getBoundTightenings().exists( tightening ) )
                tighteningSplit = split;
        }

        String isNegActive = isSplitActive( tighteningSplit ) ? "(not a" : "a";
        String suffix = isSplitActive( tighteningSplit ) ? ")" : " ";
        negatedSplitClause += isNegActive + identifier + suffix;
    }
}

String AletheProofWriter::convertTableauAssumptionToClause( unsigned index ) const
{
    return String( "(not e" ) + std::to_string( index ) + ")";
}

void AletheProofWriter::writeDelegatedLeaf( const UnsatCertificateNode *node )
{
    String proofHole = String( "(step r" + std::to_string( node->getId() ) ) + " (cl " +
                       getNegatedSplitsClause( getPathSplits( node ) ) + "):rule hole)\n";

    List<Tightening> deps = {};
    for ( const auto &split : getPathSplits( node ) )
        for ( const auto tightening : split.getBoundTightenings() )
            deps.append( tightening );

    _nodeToSplits.insert( node->getId(), deps );
    _proof.append( proofHole );
}

void AletheProofWriter::deleteProof()
{
    _assumptions.clear();
    _plcSteps.clear();
    _preprocessSteps.clear();
    _finalBoundSteps.clear();
    _proof.clear();
}

const Set<PiecewiseLinearFunctionType> AletheProofWriter::getSupportedActivations()
{
    return { RELU };
}

void AletheProofWriter::writeSimpleBoundContradiction( unsigned inconsistentVar )
{
    String varStr = std::to_string( inconsistentVar );
    String contradiction = String("(step cont (cl u" ) + varStr + " l" + varStr + "):rule la_generic :args(1 1))\n";
    contradiction += String( "(step final (cl):rule resolution :premises(cont u" ) + varStr + " l" + varStr + "))\n";
    _proof.append( contradiction );
}

void AletheProofWriter::writeEquationPreprocessingLemma( const Equation &equation, const String &equationPremise,
                                                        const Tightening &tightening )
{
    // Collect equation coefficients.
    mpq_class exactNumerator( equation._scalar );
    String boundLiterals;

    std::map<unsigned, mpq_class> coefficients;
    for ( const auto &addend : equation._addends )
        coefficients[addend._variable] += mpq_class( addend._coefficient );

    const unsigned target = tightening._variable;
    const mpq_class a = coefficients[target];
    ASSERT( a != 0 );

    const bool isUpper = tightening._type == Tightening::UB;

    // Normalize the equation coefficient of the target variable.
    mpq_class equationMultiplier( isUpper ? 1 : -1 );
    equationMultiplier /= a;
    const String boundSymbol = isUpper ? "u" : "l";
    String args = String( "(1 " ) + equationMultiplier.get_str();
    String premises = equationPremise;

    for ( const auto &entry : coefficients )
    {
        const unsigned variable = entry.first;

        if ( variable == target || entry.second == 0 )
            continue;

        const mpq_class ratio = entry.second / a;

        // Select the bound that justifies the tightening.
        const bool useUpper = isUpper ? ratio < 0 : ratio > 0;
        const Tightening::BoundType boundType = useUpper ? Tightening::UB : Tightening::LB;
        const Map<unsigned, double> &initialBounds = useUpper ? _initialUpperBounds  : _initialLowerBounds;
        const Map<unsigned, double> &preprocessedBounds = useUpper ? _preprocessedUpperBounds : _preprocessedLowerBounds;
        double value;

        if ( preprocessedBounds.exists( variable ) )
            value = preprocessedBounds[variable];
        else if ( initialBounds.exists( variable ) )
            value = initialBounds[variable];
        else if ( _reluBaseUpperVars.exists( variable ) )
        {
            ASSERT( _initialUpperBounds.exists( variable ) || _addedUpperBounds.exists( variable ) ||
                            _initialLowerBounds.exists( variable ) || _addedLowerBounds.exists( variable ) );
            if ( useUpper )
                value = _initialUpperBounds.exists( variable ) ? _initialUpperBounds[variable]
                                                                   : _addedUpperBounds[variable];
            else
                value = _initialLowerBounds.exists( variable ) ? _initialLowerBounds[variable]
                                                               : _addedLowerBounds[variable];
        }
        else
        {
            ASSERT( false );
            return;
        }

        exactNumerator -= entry.second * mpq_class( value );

        const Tightening premiseBound( variable, value, boundType );

        boundLiterals += String( " (not " ) + getBoundAsClause( premiseBound ) + ")";
        const mpq_class multiplier = -ratio;
        args += String( " " ) + multiplier.get_str();

        premises += String( " " ) + preprocessingBoundPremise( variable, boundType );
    }

    const mpq_class exactBound = exactNumerator / a;

    double correctedBound = tightening._value;

    const auto tooStrong = [&]( double candidate )
    {
        const mpq_class rationalCandidate( candidate );
        return isUpper ? rationalCandidate < exactBound  : rationalCandidate > exactBound;
    };

    if ( tooStrong( correctedBound ) )
    {
        correctedBound = exactBound.get_d();

        if ( tooStrong( correctedBound ) )
        {
            correctedBound = std::nextafter(correctedBound, isUpper
            ? std::numeric_limits<double>::infinity() : -std::numeric_limits<double>::infinity() );
        }
    }

    ASSERT( std::isfinite( correctedBound ) );
    ASSERT( !tooStrong( correctedBound ) );

    const Tightening correctedTightening( target, correctedBound, tightening._type );
    const String conclusion = getBoundAsClause( correctedTightening );
    const String clause = String( "(cl " ) + conclusion + " (not " + equationPremise + ")" + boundLiterals;
    const String id = String( "ppeq_" ) + std::to_string( _nextPreprocessingBoundId++ );
    const String resultId = id + "_bound";
    const String farkasStep = String( "(step " ) + id + " " + clause + ") :rule la_generic :args" + args + "))\n";
    const String resolutionStep = String( "(step " ) + resultId + " (cl " + conclusion +
            ") :rule resolution :premises(" + id + " " + premises + "))\n";

    updatePreprocessingBound( correctedTightening );
    setPreprocessingBoundPremise( correctedTightening, resultId );

    _preprocessSteps.append( { farkasStep, resolutionStep } );
}

void AletheProofWriter::updatePreprocessingBound( const Tightening &tightening )
{
    Map<unsigned, double> &bounds = tightening._type == Tightening::UB ? _preprocessedUpperBounds : _preprocessedLowerBounds;

    if ( bounds.exists( tightening._variable ) )
        bounds[tightening._variable] = tightening._value;
    else
        bounds.insert( tightening._variable, tightening._value );
}

String AletheProofWriter::preprocessingBoundPremise( unsigned variable, Tightening::BoundType type ) const
{
    const bool upper = type == Tightening::UB;
    const Map<unsigned, String> &proofs = upper ? _preprocessedUpperPremises : _preprocessedLowerPremises;

    if ( proofs.exists( variable ) )
        return proofs[variable];

    const String id = std::to_string( variable );

    if ( !upper && _reluBaseLowerVars.exists( variable ) )
        return String( "base_l" ) + id;

    if ( upper && _reluBaseUpperVars.exists( variable ) )
        return String( "base_u" ) + id;

    const Map<unsigned, double> &initial = upper ? _initialUpperBounds : _initialLowerBounds;

    if ( initial.exists( variable ) )
        return String( upper ? "input_u" : "input_l" ) + id;

    ASSERT( false );
    return "";
}

void AletheProofWriter::setPreprocessingBoundPremise( const Tightening &bound, const String &premise )
{
    Map<unsigned, String> &proofs = bound._type == Tightening::UB ? _preprocessedUpperPremises
                                                                  : _preprocessedLowerPremises;

    if ( proofs.exists( bound._variable ) )
        proofs[bound._variable] = premise;
    else
        proofs.insert( bound._variable, premise );
}

void AletheProofWriter::addFinalBoundStep( unsigned variable, Tightening::BoundType type, double value, const String &premise )
{
    const String id = String( type == Tightening::UB ? "u" : "l" ) + std::to_string( variable );
    const String bound = getBoundAsClause( Tightening( variable, value, type ) );

    _finalBoundSteps.append( String( "(step " ) + id + " (cl (!" + bound + " :named " + id +
            ")) :rule reordering :premises (" + premise + "))\n" );
}

void AletheProofWriter::writeFinalPreprocessingBounds()
{
    _finalBoundSteps.clear();

    Set<unsigned> upperEmitted;
    Set<unsigned> lowerEmitted;

    const auto addUpper =
            [this, &upperEmitted]( unsigned var )
            {
                if ( upperEmitted.exists( var ) )
                    return;

                double value;

                if ( _preprocessedUpperBounds.exists( var ) )
                    value = _preprocessedUpperBounds[var];
                else if ( _initialUpperBounds.exists( var ) )
                    value = _initialUpperBounds[var];
                else if ( _reluBaseUpperVars.exists( var ) && _addedUpperBounds.exists( var ) )
                    value = _addedUpperBounds[var];
                else
                    return;

                addFinalBoundStep( var, Tightening::UB, value, preprocessingBoundPremise( var, Tightening::UB ) );
                upperEmitted.insert( var );
            };

    const auto addLower =
            [this, &lowerEmitted]( unsigned var )
            {
                if ( lowerEmitted.exists( var ) )
                    return;

                double value;

                if ( _preprocessedLowerBounds.exists( var ) )
                    value = _preprocessedLowerBounds[var];
                else if ( _initialLowerBounds.exists( var ) )
                    value = _initialLowerBounds[var];
                else if ( _reluBaseLowerVars.exists( var ) && _addedLowerBounds.exists( var ) )
                    value = _addedLowerBounds[var];
                else
                    return;

                addFinalBoundStep( var,  Tightening::LB, value,preprocessingBoundPremise(var, Tightening::LB ) );
                lowerEmitted.insert( var );
            };

    for ( const auto &entry : _initialUpperBounds )
        if ( !_reluBaseUpperVars.exists( entry.first ) && entry.second != std::numeric_limits<double>::max() )
            addUpper( entry.first );

    for ( const auto &entry : _initialLowerBounds )
        if ( !_reluBaseLowerVars.exists( entry.first ) && entry.second != -std::numeric_limits<double>::max() )
            addLower( entry.first );

    for ( const auto &entry : _preprocessedUpperBounds )
        addUpper( entry.first );

    for ( const auto &entry : _preprocessedLowerBounds )
        addLower( entry.first );

    for ( auto *plc : _plc )
    {
        if ( plc->getType() != RELU )
            continue;

        const auto *relu = static_cast<const ReluConstraint *>( plc );

        addLower( relu->getF() );
        addLower( relu->getAux() );
        addUpper( relu->getAux() );
    }
}

void AletheProofWriter::registerPreprocessingSlackBound( unsigned variable, Tightening::BoundType type )
{
    Map<unsigned, double> &bounds = type == Tightening::LB ? _preprocessedLowerBounds : _preprocessedUpperBounds;
    Map<unsigned, String> &premises = type == Tightening::LB ? _preprocessedLowerPremises : _preprocessedUpperPremises;

    ASSERT( !bounds.exists( variable ) );
    ASSERT( !premises.exists( variable ) );

    const String premise = String( type == Tightening::LB ? "base_l" : "base_u" ) + std::to_string( variable );

    bounds.insert( variable, 0.0 );
    premises.insert( variable, premise );
}

void AletheProofWriter::writePreprocessingBoundHole( const Tightening &tightening )
{
    const bool isUpper = tightening._type == Tightening::UB;
    const unsigned variable = tightening._variable;
    const double value = tightening._value;

    if (value == std::numeric_limits<double>::max() || value == -std::numeric_limits<double>::max())
        return;

    Map<unsigned, double> &bounds = isUpper ? _preprocessedUpperBounds : _preprocessedLowerBounds;

    // Ignore bounds that do not improve the known bound.
    if ( bounds.exists( variable ) )
    {
        const bool improved = isUpper ? FloatUtils::lt( value, bounds[variable] )
                                      : FloatUtils::gt( value, bounds[variable] );

        if ( !improved )
            return;
    }

    const String id = String( "pp_hole_" ) + ( isUpper ? "u" : "l" ) +
            std::to_string( variable ) + "_" +std::to_string( _nextPreprocessingBoundId++ );

    _preprocessSteps.append(  String( "(step " ) + id + " (cl " + getBoundAsClause( tightening ) +
            "):rule hole)\n" );

    updatePreprocessingBound( tightening );
    setPreprocessingBoundPremise( tightening, id );
}