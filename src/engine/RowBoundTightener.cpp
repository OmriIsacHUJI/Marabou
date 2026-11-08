/*********************                                                        */
/*! \file RowBoundTightener.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz
 ** This file is part of the Marabou project.
 ** Copyright (c) 2017-2024 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved. See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 **/

#include "RowBoundTightener.h"

#include "Debug.h"
#include "InfeasibleQueryException.h"
#include "SparseUnsortedList.h"
#include "Statistics.h"

#include <cmath>
#include <limits>

inline double roundDown( double x )
{
    return std::nextafter( x, -std::numeric_limits<double>::infinity() );
}

inline double roundUp( double x )
{
    return std::nextafter( x, std::numeric_limits<double>::infinity() );
}

inline double conservativeBound( double value, Tightening::BoundType type )
{
    double ABS_TOLERANCE = GlobalConfiguration::BOUND_COMPARISON_ADDITIVE_TOLERANCE;
    double REL_TOLERANCE = GlobalConfiguration::BOUND_COMPARISON_MULTIPLICATIVE_TOLERANCE;

    if ( !std::isfinite( value ) )
        return value;

    double delta = ABS_TOLERANCE + REL_TOLERANCE * std::abs( value );

    if ( type == Tightening::UB )
        return std::nextafter( value + delta, std::numeric_limits<double>::infinity() );

    return std::nextafter( value - delta, -std::numeric_limits<double>::infinity() );
}

struct Term
{
    unsigned index;
    double coefficient;
    double lowerContribution;
    double upperContribution;
};

RowBoundTightener::RowBoundTightener( const ITableau &tableau )
    : _tableau( tableau )
    , _boundManager( tableau.getBoundManager() )
    , _lowerBounds( nullptr )
    , _upperBounds( nullptr )
    , _rows( NULL )
    , _z( NULL )
    , _ciTimesLb( NULL )
    , _ciTimesUb( NULL )
    , _ciSign( NULL )
    , _statistics( NULL )
{
}

void RowBoundTightener::setDimensions()
{
    freeMemoryIfNeeded();

    _n = _tableau.getN();
    _m = _tableau.getM();

    if ( GlobalConfiguration::EXPLICIT_BASIS_BOUND_TIGHTENING_TYPE ==
         GlobalConfiguration::COMPUTE_INVERTED_BASIS_MATRIX )
    {
        _rows = new TableauRow *[_m];
        for ( unsigned i = 0; i < _m; ++i )
            _rows[i] = new TableauRow( _n - _m );
    }
    else if ( GlobalConfiguration::EXPLICIT_BASIS_BOUND_TIGHTENING_TYPE ==
              GlobalConfiguration::USE_IMPLICIT_INVERTED_BASIS_MATRIX )
    {
        _rows = new TableauRow *[_m];
        for ( unsigned i = 0; i < _m; ++i )
            _rows[i] = new TableauRow( _n - _m );

        _z = new double[_m];
    }

    _ciTimesLb = new double[_n];
    _ciTimesUb = new double[_n];
    _ciSign = new char[_n];
}

RowBoundTightener::~RowBoundTightener()
{
    freeMemoryIfNeeded();
}

void RowBoundTightener::freeMemoryIfNeeded()
{
    if ( _rows )
    {
        for ( unsigned i = 0; i < _m; ++i )
            delete _rows[i];
        delete[] _rows;
        _rows = NULL;
    }

    if ( _z )
    {
        delete[] _z;
        _z = NULL;
    }

    if ( _ciTimesLb )
    {
        delete[] _ciTimesLb;
        _ciTimesLb = NULL;
    }

    if ( _ciTimesUb )
    {
        delete[] _ciTimesUb;
        _ciTimesUb = NULL;
    }

    if ( _ciSign )
    {
        delete[] _ciSign;
        _ciSign = NULL;
    }
}

void RowBoundTightener::examineImplicitInvertedBasisMatrix( bool untilSaturation )
{
    /*
      Roughly (the dimensions don't add up):

         xB = inv(B)*b - inv(B)*An
    */

    // Find z = inv(B) * b, by solving the forward transformation Bz = b
    _tableau.forwardTransformation( _tableau.getRightHandSide(), _z );
    for ( unsigned i = 0; i < _m; ++i )
    {
        _rows[i]->_scalar = _z[i];
        _rows[i]->_lhs = _tableau.basicIndexToVariable( i );
    }

    // Now, go over the columns of the constraint martrix, perform an FTRAN
    // for each of them, and populate the rows.
    for ( unsigned i = 0; i < _n - _m; ++i )
    {
        unsigned nonBasic = _tableau.nonBasicIndexToVariable( i );
        const double *ANColumn = _tableau.getAColumn( nonBasic );
        _tableau.forwardTransformation( ANColumn, _z );

        for ( unsigned j = 0; j < _m; ++j )
        {
            _rows[j]->_row[i]._var = nonBasic;
            _rows[j]->_row[i]._coefficient = -_z[j];
        }
    }

    // We now have all the rows, can use them for tightening.
    // The tightening procedure may throw an exception, in which case we need
    // to release the rows.
    unsigned newBoundsLearned;
    unsigned maxNumberOfIterations =
        untilSaturation ? GlobalConfiguration::ROW_BOUND_TIGHTENER_SATURATION_ITERATIONS : 1;
    do
    {
        newBoundsLearned = onePassOverInvertedBasisRows();

        if ( _statistics && ( newBoundsLearned > 0 ) )
            _statistics->incLongAttribute( Statistics::NUM_TIGHTENINGS_FROM_EXPLICIT_BASIS,
                                           newBoundsLearned );

        --maxNumberOfIterations;
    }
    while ( ( maxNumberOfIterations != 0 ) && ( newBoundsLearned > 0 ) );
}

void RowBoundTightener::examineInvertedBasisMatrix( bool untilSaturation )
{
    /*
      Roughly (the dimensions don't add up):

         xB = inv(B)*b - inv(B)*An

      We compute one row at a time.
    */

    const double *b = _tableau.getRightHandSide();
    const double *invB = _tableau.getInverseBasisMatrix();

    try
    {
        for ( unsigned i = 0; i < _m; ++i )
        {
            TableauRow *row = _rows[i];
            // First, compute the scalar, using inv(B)*b
            row->_scalar = 0;
            for ( unsigned j = 0; j < _m; ++j )
                row->_scalar += ( invB[i * _m + j] * b[j] );

            // Now update the row's coefficients for basic variable i
            for ( unsigned j = 0; j < _n - _m; ++j )
            {
                row->_row[j]._var = _tableau.nonBasicIndexToVariable( j );

                // Dot product of the i'th row of inv(B) with the appropriate
                // column of An

                const SparseUnsortedList *column = _tableau.getSparseAColumn( row->_row[j]._var );
                row->_row[j]._coefficient = 0;

                for ( const auto &entry : *column )
                    row->_row[j]._coefficient -= invB[i * _m + entry._index] * entry._value;
            }

            // Store the lhs variable
            row->_lhs = _tableau.basicIndexToVariable( i );
        }

        // We now have all the rows, can use them for tightening.
        // The tightening procedure may throw an exception, in which case we need
        // to release the rows.

        unsigned newBoundsLearned;
        unsigned maxNumberOfIterations =
            untilSaturation ? GlobalConfiguration::ROW_BOUND_TIGHTENER_SATURATION_ITERATIONS : 1;
        do
        {
            newBoundsLearned = onePassOverInvertedBasisRows();

            if ( _statistics && ( newBoundsLearned > 0 ) )
                _statistics->incLongAttribute( Statistics::NUM_TIGHTENINGS_FROM_EXPLICIT_BASIS,
                                               newBoundsLearned );

            --maxNumberOfIterations;
        }
        while ( ( maxNumberOfIterations != 0 ) && ( newBoundsLearned > 0 ) );
    }
    catch ( ... )
    {
        delete[] invB;
        throw;
    }

    delete[] invB;
}

unsigned RowBoundTightener::onePassOverInvertedBasisRows()
{
    unsigned newBounds = 0;

    for ( unsigned i = 0; i < _m; ++i )
        newBounds += tightenOnSingleInvertedBasisRow( *( _rows[i] ) );

    return newBounds;
}

unsigned RowBoundTightener::tightenOnSingleInvertedBasisRow( const TableauRow &row )
{
    /*
      A row is of the form

         y = sum ci xi + b

      We wish to tighten once for y, but also once for every x.
    */
    unsigned n = _tableau.getN();
    unsigned m = _tableau.getM();

    unsigned result = 0;

    // Compute ci * lb, ci * ub, flag signs for all entries
    enum {
        ZERO = 0,
        POSITIVE = 1,
        NEGATIVE = 2,
    };

    for ( unsigned i = 0; i < n - m; ++i )
    {
        double ci = row[i];

        if ( FloatUtils::isZero( ci ) )
        {
            _ciSign[i] = ZERO;
            _ciTimesLb[i] = 0;
            _ciTimesUb[i] = 0;
            continue;
        }

        _ciSign[i] = FloatUtils::isPositive( ci ) ? POSITIVE : NEGATIVE;

        unsigned xi = row._row[i]._var;
        _ciTimesLb[i] = ci * getLowerBound( xi );
        _ciTimesUb[i] = ci * getUpperBound( xi );
    }

    // Start with a pass for y
    unsigned y = row._lhs;
    double upperBound = row._scalar;
    double lowerBound = row._scalar;

    unsigned xi;
    double ci;

    for ( unsigned i = 0; i < n - m; ++i )
    {
        if ( _ciSign[i] == POSITIVE )
        {
            lowerBound += _ciTimesLb[i];
            upperBound += _ciTimesUb[i];
        }
        else
        {
            lowerBound += _ciTimesUb[i];
            upperBound += _ciTimesLb[i];
        }
    }

    result += registerTighterLowerBound(
        y,
        lowerBound - GlobalConfiguration::EXPLICIT_BASIS_BOUND_TIGHTENING_ROUNDING_CONSTANT,
        row );
    result += registerTighterUpperBound(
        y,
        upperBound + GlobalConfiguration::EXPLICIT_BASIS_BOUND_TIGHTENING_ROUNDING_CONSTANT,
        row );
    if ( FloatUtils::gt( getLowerBound( y ), getUpperBound( y ) ) )
    {
        ASSERT(
            FloatUtils::gt( _boundManager.getLowerBound( y ), _boundManager.getUpperBound( y ) ) );
        throw InfeasibleQueryException();
    }

    // Next, do a pass for each of the rhs variables.
    // For this, we wish to logically transform the equation into:
    //
    //     xi = 1/ci * ( y - sum cj xj - b )
    //
    // And then compute the upper/lower bounds for xi.
    //
    // However, for efficiency, we compute the lower and upper
    // bounds of the expression:
    //
    //         y - sum ci xi - b
    //
    // Then, when we consider xi we adjust the computed lower and upper
    // boudns accordingly.

    double auxLb = getLowerBound( y ) - row._scalar;
    double auxUb = getUpperBound( y ) - row._scalar;

    // Now add ALL xi's
    for ( unsigned i = 0; i < n - m; ++i )
    {
        if ( _ciSign[i] == NEGATIVE )
        {
            auxLb -= _ciTimesLb[i];
            auxUb -= _ciTimesUb[i];
        }
        else
        {
            auxLb -= _ciTimesUb[i];
            auxUb -= _ciTimesLb[i];
        }
    }

    // Now consider each individual xi
    for ( unsigned i = 0; i < n - m; ++i )
    {
        // If ci = 0, nothing to do.
        if ( _ciSign[i] == ZERO ||
             FloatUtils::lt( abs( row[i] ),
                             GlobalConfiguration::MINIMAL_COEFFICIENT_FOR_TIGHTENING ) )
            continue;

        lowerBound = auxLb;
        upperBound = auxUb;

        // Adjust the aux bounds to remove xi
        if ( _ciSign[i] == NEGATIVE )
        {
            lowerBound += _ciTimesLb[i];
            upperBound += _ciTimesUb[i];
        }
        else
        {
            lowerBound += _ciTimesUb[i];
            upperBound += _ciTimesLb[i];
        }

        // Now divide everything by ci, switching signs if needed.
        ci = row[i];
        lowerBound = lowerBound / ci;
        upperBound = upperBound / ci;

        if ( _ciSign[i] == NEGATIVE )
        {
            double temp = upperBound;
            upperBound = lowerBound;
            lowerBound = temp;
        }

        // If a tighter bound is found, store it
        xi = row._row[i]._var;
        result += registerTighterLowerBound(
            xi,
            lowerBound - GlobalConfiguration::EXPLICIT_BASIS_BOUND_TIGHTENING_ROUNDING_CONSTANT,
            row );
        result += registerTighterUpperBound(
            xi,
            upperBound + GlobalConfiguration::EXPLICIT_BASIS_BOUND_TIGHTENING_ROUNDING_CONSTANT,
            row );
        if ( FloatUtils::gt( getLowerBound( xi ), getUpperBound( xi ) ) )
        {
            ASSERT( FloatUtils::gt( _boundManager.getLowerBound( xi ),
                                    _boundManager.getUpperBound( xi ) ) );
            throw InfeasibleQueryException();
        }
    }

    return result;
}

void RowBoundTightener::examineConstraintMatrix( bool untilSaturation )
{
    unsigned newBoundsLearned;

    /*
      If working until saturation, do single passes over the matrix until no new bounds
      are learned. Otherwise, just do a single pass.
    */
    unsigned maxNumberOfIterations =
        untilSaturation ? GlobalConfiguration::ROW_BOUND_TIGHTENER_SATURATION_ITERATIONS : 1;
    do
    {
        newBoundsLearned = onePassOverConstraintMatrix();

        if ( _statistics && ( newBoundsLearned > 0 ) )
            _statistics->incLongAttribute( Statistics::NUM_TIGHTENINGS_FROM_CONSTRAINT_MATRIX,
                                           newBoundsLearned );

        --maxNumberOfIterations;
    }
    while ( ( maxNumberOfIterations != 0 ) && ( newBoundsLearned > 0 ) );
}

unsigned RowBoundTightener::onePassOverConstraintMatrix()
{
    unsigned result = 0;

    unsigned m = _tableau.getM();

    for ( unsigned i = 0; i < m; ++i )
        result += tightenOnSingleConstraintRow( i );

    return result;
}

unsigned RowBoundTightener::tightenOnSingleConstraintRow( unsigned row )
{
    /*
      A constraint matrix row satisfies:

          sum_i ci * xi = b[row]

      For each target variable xj, derive:

          xj = ( b[row] - sum_{i != j} ci * xi ) / cj

      All intermediate operations are rounded outward to
      obtain conservative lower and upper bounds.

      Prefix and suffix sums avoid subtracting the target's
      contribution from an aggregate containing that target.
    */

    const SparseUnsortedList *sparseRow = _tableau.getSparseARow( row );

    const double *b = _tableau.getRightHandSide();
    Vector<Term> terms;

    // The row coefficients and RHS must represent finite values.
    if ( !std::isfinite( b[row] ) )
        return 0;

    /*
      Step 1: Compute conservative bounds for each term ci * xi.

      The sign of ci determines which variable bound gives
      the smallest or largest contribution.
    */
    for ( const auto &entry : *sparseRow )
    {
        const unsigned index = entry._index;
        const double ci = entry._value;

        if ( !std::isfinite( ci ) )
            return 0;

        // A zero coefficient contributes nothing.
        if ( ci == 0 )
            continue;

        const double lb = getLowerBound( index );
        const double ub = getUpperBound( index );

        if ( std::isnan( lb ) || std::isnan( ub ) )
            return 0;

        // Infinite source bounds are permitted.
        const double minInput = ci > 0 ? lb : ub;
        const double maxInput = ci > 0 ? ub : lb;

        const double lowerContribution = roundDown( ci * minInput );

        const double upperContribution = roundUp( ci * maxInput );

        terms.append( { index, ci, lowerContribution, upperContribution } );
    }

    const unsigned n = terms.size();

    if ( n == 0 )
        return 0;

    /*
      Step 2: Compute prefix and suffix interval sums.

      prefixLB[k] bounds the sum of terms [0, k).
      suffixLB[k] bounds the sum of terms [k, n).

      Every addition is rounded outward.
    */
    Vector<double> prefixLB( n + 1, 0.0 );
    Vector<double> prefixUB( n + 1, 0.0 );
    Vector<double> suffixLB( n + 1, 0.0 );
    Vector<double> suffixUB( n + 1, 0.0 );

    for ( unsigned i = 0; i < n; ++i )
    {
        prefixLB[i + 1] = roundDown( prefixLB[i] + terms[i].lowerContribution );
        prefixUB[i + 1] = roundUp( prefixUB[i] + terms[i].upperContribution );
    }

    for ( unsigned i = n; i-- > 0; )
    {
        suffixLB[i] = roundDown( suffixLB[i + 1] + terms[i].lowerContribution );
        suffixUB[i] = roundUp( suffixUB[i + 1] + terms[i].upperContribution );
    }

    // Indeterminate operations involving infinities may yield NaN.
    // In that case, conservatively skip the row.
    for ( unsigned i = 0; i <= n; ++i )
        if ( std::isnan( prefixLB[i] ) || std::isnan( prefixUB[i] ) || std::isnan( suffixLB[i] ) ||
             std::isnan( suffixUB[i] ) )
            return 0;

    /*
      Step 3: Tighten each variable.

      For target xj, compute the sum of all OTHER terms
      using the corresponding prefix and suffix intervals.
    */
    unsigned result = 0;

    for ( unsigned i = 0; i < n; ++i )
    {
        const unsigned index = terms[i].index;
        const double ci = terms[i].coefficient;

        // Sum all contributions except that of the target.
        const double otherLB = roundDown( prefixLB[i] + suffixLB[i + 1] );
        const double otherUB = roundUp( prefixUB[i] + suffixUB[i + 1] );

        // Bound b[row] - sum(other terms).
        const double numeratorLB = roundDown( b[row] - otherUB );
        const double numeratorUB = roundUp( b[row] - otherLB );

        double lowerBound;
        double upperBound;

        // Division by a negative coefficient reverses the bounds.
        if ( ci > 0 )
        {
            lowerBound = roundDown( numeratorLB / ci );
            upperBound = roundUp( numeratorUB / ci );
        }
        else
        {
            lowerBound = roundDown( numeratorUB / ci );
            upperBound = roundUp( numeratorLB / ci );
        }

        /*
          Skip unusable candidates.

          An unbounded or indeterminate result must not be
          registered as a finite tightening.
        */
        if ( GlobalConfiguration::WRITE_ALETHE_PROOF )
        {
            upperBound = conservativeBound( upperBound, Tightening::UB );
            lowerBound = conservativeBound( lowerBound, Tightening::LB );
        }

        if ( std::isfinite( lowerBound ) )
            result += registerTighterLowerBound( index, lowerBound, *sparseRow );

        if ( std::isfinite( upperBound ) )
            result += registerTighterUpperBound( index, upperBound, *sparseRow );

        // Preserve the original infeasibility detection.
        if ( FloatUtils::gt( getLowerBound( index ), getUpperBound( index ) ) )
            throw InfeasibleQueryException();
    }

    return result;
}

void RowBoundTightener::examinePivotRow()
{
    if ( _statistics )
        _statistics->incLongAttribute( Statistics::NUM_ROWS_EXAMINED_BY_ROW_TIGHTENER );

    const TableauRow &row( *_tableau.getPivotRow() );
    unsigned newBoundsLearned = tightenOnSingleInvertedBasisRow( row );

    if ( _statistics && ( newBoundsLearned > 0 ) )
        _statistics->incLongAttribute( Statistics::NUM_TIGHTENINGS_FROM_ROWS, newBoundsLearned );
}

void RowBoundTightener::getRowTightenings( List<Tightening> &tightenings ) const
{
    _boundManager.getTightenings( tightenings );
}

void RowBoundTightener::setStatistics( Statistics *statistics )
{
    _statistics = statistics;
}

void RowBoundTightener::setBoundsPointers( const double *lower, const double *upper )
{
    _lowerBounds = lower;
    _upperBounds = upper;
}

//
// Local Variables:
// compile-command: "make -C ../.. "
// tags-file-name: "../../TAGS"
// c-basic-offset: 4
// End:
//
