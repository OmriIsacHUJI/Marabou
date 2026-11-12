/*********************                                                        */
/*! \file Test_SmtLibWriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Omri Isac, Guy Katz
 ** This file is part of the Marabou project.
 ** Copyright (c) 2017-2022 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved. See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 **/

#include "AletheProofWriter.h"
#include "CSRMatrix.h"
#include "MockFile.h"
#include "Query.h"
#include "context/cdlist.h"
#include "context/context.h"

#include <cxxtest/TestSuite.h>

using CVC4::context::Context;
using namespace CVC4::context;

class AletheProofWriterTestSuite : public CxxTest::TestSuite
{
public:
    MockFile *file;
    Context *context;

    void setUp()
    {
        TS_ASSERT_THROWS_NOTHING( file = new MockFile() );
        TS_ASSERT_THROWS_NOTHING( context = new Context );
    }

    void tearDown()
    {
        TS_ASSERT_THROWS_NOTHING( delete file; );
        TS_ASSERT_THROWS_NOTHING( delete context; );
    }

    /*
      Tests the writing Alethe assumption in correct SMTLIB format
    */
    void test_alethe_assumption_writing()
    {
        // Construct all required info, assuming additional aux vars and equations (post preprocessing)
        Vector<double> row = { 1, 2, -1 }; // excluding scalar
        Map<unsigned, double> ubs;
        Map<unsigned, double> lbs;
        for ( unsigned i = 0; i < row.size(); ++i )
        {
            ubs.insert( i,1 );
            lbs.insert( i,0 );
        }

        unsigned n = ubs.size();

        GroundBoundManager gbm = GroundBoundManager( *context );
        gbm.initialize( n );

        Query query = Query();
        query.setNumberOfVariables( n );
        ReluConstraint relu = ReluConstraint( 0, 1 );
        relu.transformToUseAuxVariables( query );

        Equation rowEq = Equation();
        rowEq.setScalar( 0 );
        for ( unsigned i = 0; i < row.size(); ++i )
            rowEq.addAddend( row[i], i );

        AletheProofWriter writer( ubs, lbs, gbm, { rowEq }, { &relu } );
        // Initialize tableau with info, that includes one more aux equation and two more aux variables
        writer.initializeTableau( 2, Vector<double>( n + 2, 1 ), Vector<double>( n + 2, 0 ), NULL, { &relu } );
        writer.writeInstanceToFile( *file );

        String line;
        String expectedLine;

        // Tableau assumptions (before preprocessing)
        line = file->readLine( '\n' );
        expectedLine = "(assume e0(!(= (! 0.0 :named pp_rhs_0)(+ x0 (* 2.0 x1) (- x2))):named e0))";
        TS_ASSERT_EQUALS( line, expectedLine );

        // Bound Assumptions
        line = file->readLine( '\n' );
        expectedLine = "(assume input_u0 (!(<= x0 1.0):named input_u0))";
        TS_ASSERT_EQUALS( line, expectedLine );

        line = file->readLine( '\n' );
        expectedLine = "(assume input_u1 (!(<= x1 1.0):named input_u1))";
        TS_ASSERT_EQUALS( line, expectedLine );

        line = file->readLine( '\n' );
        expectedLine = "(assume input_u2 (!(<= x2 1.0):named input_u2))";
        TS_ASSERT_EQUALS( line, expectedLine );

        line = file->readLine( '\n' );
        expectedLine = "(assume input_l0 (!(>= x0 0.0):named input_l0))";
        TS_ASSERT_EQUALS( line, expectedLine );

        line = file->readLine( '\n' );
        expectedLine = "(assume input_l2 (!(>= x2 0.0):named input_l2))";
        TS_ASSERT_EQUALS( line, expectedLine );

        // Relu Assumptions  (before preprocessing)
        line = file->readLine( '\n' );
        expectedLine = "(assume relupprelu_1 (ite (!(<= 0.0 x0):named apprelu_1)(= x0 x1)(<= x1 0.0)))";
        TS_ASSERT_EQUALS( line, expectedLine );

        line = file->readLine( '\n' );
        expectedLine = "(assume base_l1 (!(>= x1 0.0):named base_l1))";
        TS_ASSERT_EQUALS( line, expectedLine );

        line = file->readLine( '\n' );
        // Next lines should represent proof steps
        while ( line != "" )
        {
            expectedLine = "(step";
            TS_ASSERT_EQUALS( line.find( expectedLine ), 0U );
            line = file->readLine( '\n' );
        }
    }
};