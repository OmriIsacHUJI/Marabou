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

#ifndef __AletheProofWriter_h__
#define __AletheProofWriter_h__
class AletheProofbWriter
{
public:
    AletheProofbWriter( unsigned explanationSize,
                        const Vector<double> &upperBounds,
                        const Vector<double> &lowerBounds,
                        const SparseMatrix *tableau,
                        const List<PiecewiseLinearConstraint *> &problemConstraints,
                        UnsatCertificateNode *root );


    void writeAletheProof( IFile &file );


private:
    const SparseMatrix *_initialTableau;
    Vector<String> _tableauAssumptions; // For easy access
    Vector<Stack<std::tuple<int, double>>> _currentUpperBounds;
    Vector<Stack<std::tuple<int, double>>> _currentLowerBounds;
    List<PiecewiseLinearConstraint *> _plc;
    UnsatCertificateNode *_root;
    List<String> _proof;
    unsigned _n;
    unsigned _m;
    unsigned _stepCounter;
    unsigned _lemmaCounter;

    unsigned writeAletheProof( const UnsatCertificateNode *node );

    void writeAssumptions();

    void writePLCAssumption();

    unsigned applyContradiction( const UnsatCertificateNode *node );

    void concludeChildrenUnsat( const UnsatCertificateNode *node,
                                unsigned index,
                                List<unsigned> childrenIndices );

    void writeInstanceToFile( IFile &file, const List<String> &instance );

    void applyAllLemmas( const UnsatCertificateNode *node );

    void
    applyReluLemma( const UnsatCertificateNode *node, const PLCLemma &lemma, ReluConstraint *plc );

    void insertCurrentBoundsToVec( bool isUpper, Vector<double> &boundsVec );

    String getPathClause( const UnsatCertificateNode *node );

    String getPathResSteps( const UnsatCertificateNode *node );

    String getSplitsAsClause( const List<PiecewiseLinearCaseSplit> &splits );

    String getSplitAsClause( const PiecewiseLinearCaseSplit &splits );

    String getBoundAsClause( const Tightening &bound );

    String convertTableauAssumptionToClause( unsigned index );

    bool isSplitActive( const PiecewiseLinearCaseSplit &split );

    void linearCombinationMpq( const std::vector<mpq_t> &explainedRow,
                               const SparseUnsortedList &expl );

    void farkasStrings( const SparseUnsortedList &expl,
                        String &farkasArgs,
                        String &farkasClause,
                        String &farkasParticipants,
                        int explainerVar,
                        bool isUpper );

    void writeDelegatedLeaf( const UnsatCertificateNode *node);
};

#endif // __AletheProofWriter_h__