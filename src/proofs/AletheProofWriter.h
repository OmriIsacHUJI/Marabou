/**
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

#ifndef __AletheProofWriter_h__
#define __AletheProofWriter_h__

#include "GroundBoundManager.h"
#include "PiecewiseLinearCaseSplit.h"
#include "SmtLibWriter.h"
#include "SparseMatrix.h"
#include "SparseUnsortedList.h"
#include "Stack.h"
#include "UnsatCertificateNode.h"
#include "UnsatCertificateUtils.h"
#include "Vector.h"
#include "gmp.h"
#include "gmpxx.h"

class AletheProofWriter
{
public:
    static const Set<PiecewiseLinearFunctionType> getSupportedActivations();

    AletheProofWriter( unsigned explanationSize,
                       const Vector<double> &upperBounds,
                       const Vector<double> &lowerBounds,
                       const GroundBoundManager &groundBoundManager,
                       const SparseMatrix *tableau,
                       const List<PiecewiseLinearConstraint *> &problemConstraints );

    /*
     Write whole proof info to a file
    */
    void writeInstanceToFile( IFile &file );

    /*
     Write steps to conclude UNSAT of a node from the UNSAT of its children
    */
    void writeChildrenConclusion( const UnsatCertificateNode *node );

    /*
     Get the next unique ID to a node, and increment it
    */
    unsigned assignId();

    /*
     Write proof hole for a delegated leaf node
    */
    void writeDelegatedLeaf( const UnsatCertificateNode *node );

    /*
      Add proof steps to prove a PLC lemma
    */
    void writeLemma( const std::shared_ptr<GroundBoundManager::GroundBoundEntry> &lemmaEntry );

    /*
     Add proof steps to prove the UNSAT of a leaf
    */
    void writeContradiction( const SparseUnsortedList &contradiction, UnsatCertificateNode *node );

    /*
     Delete the content of the proof
    */
    void deleteProof();

    /*
     Set the initial tableau constraints that define the query
    */
    void setInitialTableau( const SparseMatrix *tableau );

private:
    /*
     Initial query information.
    */
    const SparseMatrix *_initialTableau;
    Vector<String> _tableauAssumptions; // For easy access
    Vector<double> _initialUpperBounds;
    Vector<double> _initialLowerBounds;
    const GroundBoundManager &_groundBoundManager;
    Vector<PiecewiseLinearConstraint *> _plc;

    unsigned _n;
    unsigned _m;

    /*
     Lists for proofs steps and assumptions, track the number of nodes used in the proof
    */
    List<String> _proof;
    List<String> _assumptions;
    unsigned _stepCounter;

    /*
     Maintain maps the link between variables, PLC, nodes and their ids and splits
     */
    Map<unsigned, PiecewiseLinearConstraint *> _varToPlc;
    Map<unsigned, List<Tightening>> _idToSplits;
    Map<unsigned, List<Tightening>> _nodeToSplits;

    /*
     Add original query assumptions to the proof file
    */
    void writeBoundAssumptions();

    void writePLCAssumption();

    void writeTableauAssumptions();

    /*
     Add proof steps for proving a lemma learned from a ReLU activation constraint.
    */
    void writeReluLemma( const std::shared_ptr<GroundBoundManager::GroundBoundEntry> &lemmaEntry,
                         const ReluConstraint *relu );
    /*
     Collect all case splits of path to a proof node
    */
    List<PiecewiseLinearCaseSplit> getPathSplits( const UnsatCertificateNode *node ) const;

    /*
     Convert multiple Marabou objects into their corresponding Alethe clause
    */

    String getBoundAsClause( const Tightening &bound ) const;

    String getNegatedSplitsClause( const List<PiecewiseLinearCaseSplit> &splits ) const;

    String convertTableauAssumptionToClause( unsigned index ) const;

    /*
     Check if a case split object represents the active ReLU phase
    */
    bool isSplitActive( const PiecewiseLinearCaseSplit &split ) const;

    /*
     Compute linear combinations from proof vectors using GMP
    */
    void linearCombinationMpq( const std::vector<mpq_t> &explainedRow,
                               const SparseUnsortedList &expl ) const;

    /*
     A helper function that converts proof vector information to la_generic arguments and clauses as
     Strings
    */
    void farkasStrings( const SparseUnsortedList &expl,
                        unsigned entryId,
                        String &farkasArgs,
                        String &farkasClause,
                        String &farkasParticipants,
                        String &negatedSplitClause,
                        int explainerVar,
                        bool isUpper,
                        UnsatCertificateNode *node );
};

#endif // __AletheProofWriter_h__