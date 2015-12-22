// Copyright (c) 2015 Tomas Balyo, Karlsruhe Institute of Technology
/*
 * Lingeling.cpp
 *
 *  Created on: Nov 11, 2014
 *      Author: balyo
 */

#include "Lingeling.h"
#include <ctype.h>
#include "../utilities/DebugUtils.h"

extern "C" {
	#include "lglib.h"
}

int termCallback(void* solverPtr) {
	Lingeling* lp = (Lingeling*)solverPtr;
	return lp->stopSolver;
}

void produceUnit(void* sp, int lit) {
	vector<int> vcls;
	vcls.push_back(lit);
	Lingeling* lp = (Lingeling*)sp;
	lp->callback->processClause(vcls, lp->myId);
}

void produce(void* sp, int* cls, int glue) {
	// unit clause, call produceUnit
	if (cls[1] == 0) {
		produceUnit(sp, cls[0]);
		return;
	}
	Lingeling* lp = (Lingeling*)sp;
	if (glue > lp->glueLimit) {
		return;
	}
	vector<int> vcls;
	// to avoid zeros in the array, 1 is added to the glue
	vcls.push_back(1+glue);
	int i = 0;
	while (cls[i] != 0) {
		vcls.push_back(cls[i]);
		i++;
	}
	//printf("glue = %d, size = %lu\n", glue, vcls.size());
	lp->callback->processClause(vcls, lp->myId);
}

void consumeUnits(void* sp, int** start, int** end) {
	Lingeling* lp = (Lingeling*)sp;

	if (lp->unitsToAdd.empty() || (lp->clauseAddMutex.tryLock() == false)) {
		*start = lp->unitsBuffer;
		*end = lp->unitsBuffer;
		return;
	}
	if (lp->unitsToAdd.size() >= lp->unitsBufferSize) {
		lp->unitsBufferSize = 2*lp->unitsToAdd.size();
		lp->unitsBuffer = (int*)realloc((void*)lp->unitsBuffer, lp->unitsBufferSize * sizeof(int));
	}

	for (size_t i = 0; i < lp->unitsToAdd.size(); i++) {
		lp->unitsBuffer[i] = lp->unitsToAdd[i];
	}

	*start = lp->unitsBuffer;
	*end = *start + lp->unitsToAdd.size();
	lp->clauseAddMutex.unlock();
}

void consumeCls(void* sp, int** clause, int* glue) {
	Lingeling* lp = (Lingeling*)sp;

	if (lp->learnedClausesToAdd.empty()) {
		*clause = NULL;
		return;
	}
	if (lp->clauseAddMutex.tryLock() == false) {
		*clause = NULL;
		return;
	}
	vector<int> cls = lp->learnedClausesToAdd.back();
	lp->learnedClausesToAdd.pop_back();

	if (cls.size()+1 >= lp->clsBufferSize) {
		lp->clsBufferSize = 2*cls.size();
		lp->clsBuffer = (int*)realloc((void*)lp->clsBuffer, lp->clsBufferSize * sizeof(int));
	}
	// to avoid zeros in the array, 1 was added to the glue
	*glue = cls[0]-1;
	for (size_t i = 1; i < cls.size(); i++) {
		lp->clsBuffer[i-1] = cls[i];
	}
	lp->clsBuffer[cls.size()-1] = 0;
	*clause = lp->clsBuffer;
	lp->clauseAddMutex.unlock();
}

Lingeling::Lingeling() {
	solver = lglinit();
	//lglsetopt(solver, "verbose", 10);
	// BCA has to be disabled for valid clause sharing (or freeze all literals)
	lglsetopt(solver, "bca", 0);

	stopSolver = 0;
	callback = NULL;
	lglseterm(solver, termCallback, this);
	glueLimit = 2;

	unitsBufferSize = clsBufferSize = 100;
	unitsBuffer = (int*) malloc(unitsBufferSize*sizeof(int));
	clsBuffer = (int*) malloc(clsBufferSize*sizeof(int));
	myId = 0;

}

bool Lingeling::loadFormula(const char* filename) {
	vector<PortfolioSolverInterface*> solvers;
	solvers.push_back(this);
	return loadFormulaToSolvers(solvers, filename);
}

int Lingeling::getVariablesCount() {
	return lglnvars(solver);
}

// Get a variable suitable for search splitting
int Lingeling::getSplittingVariable() {
	//TODO not sure what this is?
	return lglookahead(solver);
}

// Set initial phase for a given variable
void Lingeling::setPhase(const int var, const bool phase) {
	lglsetphase(solver, phase ? var : -var);
}

// Interrupt the SAT solving, so it can be started again with new assumptions
void Lingeling::setSolverInterrupt() {
	stopSolver = 1;
}
void Lingeling::unsetSolverInterrupt() {
	stopSolver = 0;
}

// Solve the formula with a given set of assumptions
// return 10 for SAT, 20 for UNSAT, 0 for UNKNOWN
SatResult Lingeling::solve(const vector<int>& assumptions) {

	// add the clauses
	clauseAddMutex.lock();
	for (size_t i = 0; i < clausesToAdd.size(); i++) {
		for (size_t j = 0; j < clausesToAdd[i].size(); j++) {
			lgladd(solver, clausesToAdd[i][j]);
		}
		lgladd(solver, 0);
	}
	clausesToAdd.clear();
	clauseAddMutex.unlock();

	// set the assumptions
	for (size_t i = 0; i < assumptions.size(); i++) {
		// freezing problems
		lglassume(solver, assumptions[i]);
	}
	int res = lglsat(solver);
	switch (res) {
	case LGL_SATISFIABLE:
		return SAT;
	case LGL_UNSATISFIABLE:
		return UNSAT;
	}
	return UNKNOWN;
}

// Add a permanent clause to the formula
void Lingeling::addClause(vector<int>& clause) {
	clauseAddMutex.lock();
	clausesToAdd.push_back(clause);
	clauseAddMutex.unlock();
}

void Lingeling::addClauses(vector<vector<int> >& clauses) {
	clauseAddMutex.lock();
	clausesToAdd.insert(clausesToAdd.end(), clauses.begin(), clauses.end());
	clauseAddMutex.unlock();
}

void Lingeling::addInitialClauses(vector<vector<int> >& clauses) {
	for (size_t i = 0; i < clauses.size(); i++) {
		for (size_t j = 0; j < clauses[i].size(); j++) {
			int lit = clauses[i][j];
			lgladd(solver, lit);
		}
		lgladd(solver, 0);
	}
}

// Add a learned clause to the formula
void Lingeling::addLearnedClause(vector<int>& clause) {
	clauseAddMutex.lock();
	if (clause.size() == 1) {
		unitsToAdd.push_back(clause[0]);
	} else {
		learnedClausesToAdd.push_back(clause);
	}
	clauseAddMutex.unlock();
}

void Lingeling::addLearnedClauses(vector<vector<int> >& clauses) {
	clauseAddMutex.lock();
	for (size_t i = 0; i < clauses.size(); i++) {
		if (clauses[i].size() == 1) {
			unitsToAdd.push_back(clauses[i][0]);
		} else {
			learnedClausesToAdd.push_back(clauses[i]);
		}
	}
	clauseAddMutex.unlock();
}

void Lingeling::increaseClauseProduction() {
	glueLimit++;
}

void Lingeling::setLearnedClauseCallback(LearnedClauseCallback* callback, int solverId) {
	this->callback = callback;
	lglsetproducecls(solver, produce, this);
	lglsetproduceunit(solver, produceUnit, this);
	lglsetconsumeunits(solver, consumeUnits, this);
	lglsetconsumecls(solver, consumeCls, this);
	myId = solverId;
}

SolvingStatistics Lingeling::getStatistics() {
	SolvingStatistics st;
	st.conflicts = lglgetconfs(solver);
	st.decisions = lglgetdecs(solver);
	st.propagations = lglgetprops(solver);
	st.memPeak = lglmaxmb(solver);
	return st;
}

void Lingeling::diversify(int rank, int size) {
	// This method is copied from Plingeling
	lglsetopt(solver, "seed", rank);
	lglsetopt(solver, "flipping", 0);
    switch (rank % 16) {
		case 0: default: break;
		case 1: lglsetopt (solver, "plain", 1); break;
		case 2: lglsetopt (solver, "agilelim", 100); break;
		case 3: lglsetopt (solver, "block", 0), lglsetopt (solver, "cce", 0); break;
		case 4: lglsetopt (solver, "bias", -1); break;
		case 5: lglsetopt (solver, "acts", 0); break;
		case 6: lglsetopt (solver, "phase", 1); break;
		case 7: lglsetopt (solver, "acts", 1); break;
		case 8: lglsetopt (solver, "bias", 1); break;
		case 9:
			lglsetopt (solver, "wait", 0);
			lglsetopt (solver, "blkrtc", 1);
			lglsetopt (solver, "elmrtc", 1);
			break;
		case 10: lglsetopt (solver, "phase", -1); break;
		case 11: lglsetopt (solver, "prbsimplertc", 1); break;
		case 12: lglsetopt (solver, "gluescale", 1); break;
		case 13: lglsetopt (solver, "gluescale", 3); break;
		case 14: lglsetopt (solver, "move", 1); break;
		case 15: lglsetopt(solver, "flipping", 1); break;
	}
}



Lingeling::~Lingeling() {
	lglrelease(solver);
	free(unitsBuffer);
	free(clsBuffer);
}

