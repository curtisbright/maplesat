// Copyright (c) 2015 Tomas Balyo, Karlsruhe Institute of Technology
/*
 * portfolioSolverInterface.h
 *
 *  Created on: Oct 10, 2014
 *      Author: balyo
 */

#ifndef PORTFOLIOSOLVERINTERFACE_H_
#define PORTFOLIOSOLVERINTERFACE_H_

#include <vector>
using namespace std;

enum SatResult {
	SAT = 10,
	UNSAT = 20,
	UNKNOWN = 0
};

struct SolvingStatistics {
	SolvingStatistics():propagations(0),decisions(0),conflicts(0),restarts(0),memPeak(0) {}
	unsigned long propagations;
	unsigned long decisions;
	unsigned long conflicts;
	unsigned long restarts;
	double memPeak;
};

class LearnedClauseCallback {
public:
	virtual void processClause(vector<int>& cls, int solverId) = 0;
	virtual ~LearnedClauseCallback() {};
};

/**
 * Interface for solvers that can be used used in the portfolio
 */
class PortfolioSolverInterface {
public:
	// Load formula from a given dimacs file, return false if failed
	virtual bool loadFormula(const char* filename) = 0;

	// Get the number of variables of the formula
	virtual int getVariablesCount() = 0;

	// Get a variable suitable for search splitting
	virtual int getSplittingVariable() = 0;

	// Set initial phase for a given variable
	virtual void setPhase(const int var, const bool phase) = 0;

	// Interrupt the SAT solving, solving cannot continue until interrupt is unset.
	virtual void setSolverInterrupt() = 0;

	// Remove the SAT solving interrupt request.
	virtual void unsetSolverInterrupt() = 0;

	// Solve the formula with a given set of assumptions
	virtual SatResult solve(const vector<int>& assumptions = vector<int>()) = 0;

	// Add a (list of) permanent clause(s) to the formula
	virtual void addClause(vector<int>& clause) = 0;
	virtual void addClauses(vector<vector<int> >& clauses) = 0;
	virtual void addInitialClauses(vector<vector<int> >& clauses) = 0;

	// Add a (list of) learned clause(s) to the formula
	// The learned clauses might be added later or possibly never
	virtual void addLearnedClause(vector<int>& clauses) = 0;
	virtual void addLearnedClauses(vector<vector<int> >& clauses) = 0;

	// Set a function that should be called for each learned clause
	virtual void setLearnedClauseCallback(LearnedClauseCallback* callback, int solverId) = 0;

	// Request the solver to produce more clauses
	virtual void increaseClauseProduction() = 0;

	// Get solver statistics
	virtual SolvingStatistics getStatistics() = 0;

	virtual void diversify(int rank, int size) = 0;

	// destructor
	virtual ~PortfolioSolverInterface() {}
};

#endif /* PORTFOLIOSOLVERINTERFACE_H_ */
