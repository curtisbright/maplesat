// Copyright (c) 2015 Tomas Balyo, Karlsruhe Institute of Technology
/*
 * Lingeling.h
 *
 *  Created on: Nov 11, 2014
 *      Author: balyo
 */

#ifndef LINGELING_H_
#define LINGELING_H_

#include "../utilities/SatUtils.h"
#include "PortfolioSolverInterface.h"
#include "../utilities/Threading.h"

struct LGL;

class Lingeling: public PortfolioSolverInterface {

private:
	LGL* solver;
	int stopSolver;
	LearnedClauseCallback* callback;
	int glueLimit;
	Mutex clauseAddMutex;
	int myId;

	// callback friends
	friend int termCallback(void* solverPtr);
	friend void produce(void* sp, int* cls, int glue);
	friend void produceUnit(void* sp, int lit);
	friend void consumeUnits(void* sp, int** start, int** end);
	friend void consumeCls(void* sp, int** clause, int* glue);

	// clause addition
	vector<vector<int> > clausesToAdd;
	vector<vector<int> > learnedClausesToAdd;
	vector<int> unitsToAdd;
	int* unitsBuffer;
	size_t unitsBufferSize;
	int* clsBuffer;
	size_t clsBufferSize;

public:

	// Load formula from a given dimacs file, return false if failed
	bool loadFormula(const char* filename);

	// Get the number of variables of the formula
	int getVariablesCount();

	// Get a variable suitable for search splitting
	int getSplittingVariable();

	// Set initial phase for a given variable
	void setPhase(const int var, const bool phase);

	// Interrupt the SAT solving, so it can be started again with new assumptions and added clauses
	void setSolverInterrupt();
	void unsetSolverInterrupt();

	// Solve the formula with a given set of assumptions
	SatResult solve(const vector<int>& assumptions);

	// Add a (list of) permanent clause(s) to the formula
	void addClause(vector<int>& clause);
	void addClauses(vector<vector<int> >& clauses);
	void addInitialClauses(vector<vector<int> >& clauses);

	// Add a (list of) learned clause(s) to the formula
	// The learned clauses might be added later or possibly never
	void addLearnedClause(vector<int>& clauses);
	void addLearnedClauses(vector<vector<int> >& clauses);

	// Set a function that should be called for each learned clause
	void setLearnedClauseCallback(LearnedClauseCallback* callback, int solverId);

	// Request the solver to produce more clauses
	void increaseClauseProduction();

	// Get solver statistics
	SolvingStatistics getStatistics();

	void diversify(int rank, int size);

	Lingeling();
	 ~Lingeling();
};

#endif /* LINGELING_H_ */
