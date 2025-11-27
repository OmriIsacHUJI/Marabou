/**
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

#ifndef __AletheProofWriter_h__
#define __AletheProofWriter_h__

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
    AletheProofWriter( unsigned explanationSize,
                       const Vector<double> &upperBounds,
                       const Vector<double> &lowerBounds,
                       const SparseMatrix *tableau,
                       const List<PiecewiseLinearConstraint *> &problemConstraints,
                       UnsatCertificateNode *root );


    void writeAletheProof( IFile &file );

    void writeInstanceToFile( IFile &file );

    void writeAletheProof( const UnsatCertificateNode *node, bool toRecurse = false );

    unsigned assignId();


private:
    const SparseMatrix *_initialTableau;
    Vector<String> _tableauAssumptions; // For easy access
    Vector<Stack<std::tuple<int, double>>> _currentUpperBounds;
    Vector<Stack<std::tuple<int, double>>> _currentLowerBounds;
    List<PiecewiseLinearConstraint *> _plc;
    UnsatCertificateNode *_root;
    List<String> _proof;
    List<String> _assumptions;

    unsigned _n;
    unsigned _m;
    unsigned _stepCounter;

    Map<unsigned, PiecewiseLinearConstraint *> _varToPLC;

    void writeBoundAssumptions();

    void writePLCAssumption();

    void writeTableauAssumptions();

    void applyContradiction( const UnsatCertificateNode *node );

    void concludeChildrenUnsat( const UnsatCertificateNode *node, List<unsigned> childrenIndices );

    void applyAllLemmas( const UnsatCertificateNode *node );

    List<String>
    applyReluLemma( const UnsatCertificateNode *node, const PLCLemma &lemma, ReluConstraint *plc );

    void insertCurrentBoundsToVec( bool isUpper, Vector<double> &boundsVec );

    String getNegatedSplitsClause( const List<PiecewiseLinearCaseSplit> &splits ) const;

    String getSplitsResSteps( const List<PiecewiseLinearCaseSplit> &splits )const;

    List<PiecewiseLinearCaseSplit> getPathSplits( const UnsatCertificateNode *node )const;

    String getSplitsAsClause( const List<PiecewiseLinearCaseSplit> &splits )const;

    String getSplitAsClause( const PiecewiseLinearCaseSplit &split ) const;

    String getBoundAsClause( const Tightening &bound ) const;

    String convertTableauAssumptionToClause( unsigned index ) const;

    bool isSplitActive( const PiecewiseLinearCaseSplit &split )const ;

    void linearCombinationMpq( const std::vector<mpq_t> &explainedRow,
                               const SparseUnsortedList &expl )const ;

    void farkasStrings( const SparseUnsortedList &expl,
                        String &farkasArgs,
                        String &farkasClause,
                        String &farkasParticipants,
                        int explainerVar,
                        bool isUpper );

    void writeDelegatedLeaf( const UnsatCertificateNode *node );
};

#endif // __AletheProofWriter_h__