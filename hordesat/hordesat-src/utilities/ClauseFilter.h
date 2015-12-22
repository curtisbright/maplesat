// Copyright (c) 2015 Tomas Balyo, Karlsruhe Institute of Technology
/*
 * ClauseFilter.h
 *
 *  Created on: Aug 12, 2014
 *      Author: balyo
 */

#ifndef CLAUSEFILTER_H_
#define CLAUSEFILTER_H_

#include <vector>
#include <bitset>

using namespace std;

//#define NUM_BITS 268435399 // 32MB
#define NUM_BITS 26843543 // 3,2MB

class ClauseFilter {
public:
	ClauseFilter();
	virtual ~ClauseFilter();
	/**
	 * Return false if the given clause has already been registered
	 * otherwise add it to the filter and return true.
	 */
	bool registerClause(const vector<int>& cls);
	/**
	 * Clear the filter, i.e., return to its initial state.
	 */
	void clear();

private:
	bitset<NUM_BITS>* s1;
	size_t hashFunction(const vector<int>& cls, int which);
	size_t commutativeHashFunction(const vector<int>& cls, int which);

};

#endif /* CLAUSEFILTER_H_ */
