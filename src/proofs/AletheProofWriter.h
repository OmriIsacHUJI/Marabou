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

#include "IProofWriter.h"
#include "SmtLibWriter.h"
#include "SparseMatrix.h"
#include "Stack.h"
#include "UnsatCertificateUtils.h"
#include "Vector.h"
#include "gmp.h"
#include "gmpxx.h"

#include <cmath>
#include <limits>
#include <map>
#include <memory>

struct DeferredReluLemma
{
    const ReluConstraint *_relu;
    Tightening _causing;
    Tightening _affected;
    String _id;
    String _causingPremise;
};

struct PreprocessingStep
{
    String _text;
    std::shared_ptr<DeferredReluLemma> _reluLemma;
};

struct EquationProofTerms
{
    mpq_class _numerator;
    String _args;
    String _premises;
    String _literals;
};

class AletheProofWriter : public IProofWriter
{
public:
    static const Set<PiecewiseLinearFunctionType> getSupportedActivations();

    AletheProofWriter( const Map<unsigned, double> &upperBounds,
                       const Map<unsigned, double> &lowerBounds,
                       const GroundBoundManager &groundBoundManager,
                       const List<Equation> &unprocessedEquations,
                       const List<PiecewiseLinearConstraint *> &problemConstraints );

    // Called once the solver has initialized its tableau and PLC auxiliary variables.
    void initializeTableau( unsigned explanationSize,
                            const Vector<double> &upperBounds,
                            const Vector<double> &lowerBounds,
                            const SparseMatrix *tableau,
                            const List<PiecewiseLinearConstraint *> &problemConstraints ) override;

    ~AletheProofWriter() override{};

    /*
     Write whole proof info to a file
    */
    void writeInstanceToFile( IFile &file ) override;

    /*
     Write steps to conclude UNSAT of a node from the UNSAT of its children
    */
    void writeChildrenConclusion( const UnsatCertificateNode *node ) override;

    /*
     Write proof hole for a delegated leaf node
    */
    void writeDelegatedLeaf( const UnsatCertificateNode *node ) override;

    /*
      Add proof steps to prove a PLC lemma
    */
    void
    writeLemma( const std::shared_ptr<GroundBoundManager::GroundBoundEntry> &lemmaEntry ) override;

    /*
     Add proof steps to prove the UNSAT of a leaf
    */
    void writeContradiction( const SparseUnsortedList &contradiction,
                             UnsatCertificateNode *node ) override;

    /*
     Add proof steps to prove the UNSAT of a simple bound contradiction
    */
    void writeSimpleBoundContradiction( unsigned inconsistentVar ) override;

    /*
     Delete the content of the proof
    */
    void deleteProof() override;


    /*
     Producing proofs for preprocessing
    */
    void writeEquationPreprocessingLemma( const Equation &equation,
                                          const String &equationPremise,
                                          const Tightening &tightening );

    void writeReluPreprocessingLemma( const Tightening &affected,
                                      const Tightening &causing,
                                      const ReluConstraint *relu );

    void registerPreprocessingSlackBound( unsigned variable, Tightening::BoundType type );

    /*
     Prove UNSAT derivation during preprocessing
    */
    void setOriginalVariableCount( unsigned count ) override;

    /*
     Check if a tableau was initialized for the checker
    */
    bool hasTableau() const override;

    /*
     Write steps to prove preprocessing UNSAT
    */
    bool writePreprocessingContradiction() override;

    /*
     Artificially add aux vars to the constraints
     */
    void setPreprocessingConstraints( const List<PiecewiseLinearConstraint *> &constraints );

private:
    /*
     Initial query information.
    */
    const SparseMatrix *_initialTableau;
    Map<unsigned, double> _initialUpperBounds;
    Map<unsigned, double> _initialLowerBounds;

    const GroundBoundManager &_groundBoundManager;
    Vector<PiecewiseLinearConstraint *> _plc;
    Set<unsigned> _reluAuxVars;
    List<Equation> _unprocessedEquations;
    unsigned _numOfInequalities;
    unsigned _originalVariableCount;

    unsigned _n;
    unsigned _m;

    /*
     Lists for proofs steps and assumptions, track the number of nodes used in the proof
    */
    List<String> _proof;
    List<String> _assumptions;
    List<PreprocessingStep> _preprocessSteps;
    List<String> _plcSteps;
    List<String> _finalBoundSteps;

    /*
     Maintain maps the link between variables, PLC, nodes and their ids and splits
     */
    Map<unsigned, PiecewiseLinearConstraint *> _varToPlc;
    Map<unsigned, List<Tightening>> _idToSplits;
    Map<unsigned, List<Tightening>> _nodeToSplits;

    /*
     Keep track of bounds' sources
    */

    Map<unsigned, double> _addedUpperBounds;
    Map<unsigned, double> _addedLowerBounds;
    Map<unsigned, double> _preprocessedUpperBounds;
    Map<unsigned, double> _preprocessedLowerBounds;
    Map<unsigned, String> _preprocessedUpperPremises;
    Map<unsigned, String> _preprocessedLowerPremises;
    Set<unsigned> _reluBaseLowerVars;
    Set<unsigned> _reluBaseUpperVars;

    unsigned _nextPreprocessingBoundId = 0;
    unsigned _preprocessingSlackRegistrationCount = 0;
    Vector<unsigned> _preprocessingReluAuxVars;

    /*
     Helper functions for handling preprocessing and derive consistent bound names for the rest of
     the proof
     */
    bool validProofBound( double value ) const;
    bool
    preprocessingBoundValue( unsigned variable, Tightening::BoundType type, double &value ) const;
    String preprocessingBoundPremise( unsigned variable, Tightening::BoundType type ) const;
    void updatePreprocessingBound( const Tightening &bound );
    void setPreprocessingBoundPremise( const Tightening &bound, const String &premise );
    void recordPreprocessingBound( const Tightening &bound, const String &premise );

    bool isStrongerThanExact( double candidate,
                              const mpq_class &exact,
                              Tightening::BoundType type ) const;
    double outwardRoundedBound( double proposed,
                                const mpq_class &exact,
                                Tightening::BoundType type ) const;
    void collectEquationProofTerms( const std::map<unsigned, mpq_class> &coefficients,
                                    const Tightening &result,
                                    const mpq_class &targetCoefficient,
                                    EquationProofTerms &terms ) const;

    void addFinalBoundStep( unsigned variable,
                            Tightening::BoundType type,
                            double value,
                            const String &premise );
    void
    addFinalBoundIfKnown( unsigned variable, Tightening::BoundType type, Set<unsigned> &emitted );
    void writeFinalPreprocessingBounds();

    bool supportedReluPropagation( const Tightening &affected,
                                   const Tightening &cause,
                                   const ReluConstraint *relu ) const;
    Tightening reluProofConclusion( const Tightening &affected,
                                    const Tightening &cause,
                                    const ReluConstraint *relu ) const;
    String renderReluPreprocessingLemma( const DeferredReluLemma &pending );
    void writePreprocessingSteps( IFile &file );

    String reluProofIdentifier( const ReluConstraint *relu ) const;
    String reluEquationName( const ReluConstraint *relu ) const;


    /*
     Add original query assumptions to the proof file
    */
    void writeBoundAssumptions();

    void writePLCAssumption();

    void writeTableauAssumptions();

    void proveEqualityWithSlackFromInequality( Equation eq, unsigned eqIndex, unsigned auxIndex );

    /*
     Add proof steps for proving a lemma learned from a ReLU activation constraint.
    */
    String writeReluLemma( const std::shared_ptr<GroundBoundManager::GroundBoundEntry> &lemmaEntry,
                           const ReluConstraint *relu,
                           bool preprocessing = false,
                           const String &fixedId = "",
                           const String &fixedCausingPremise = "" );
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