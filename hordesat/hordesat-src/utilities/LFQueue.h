// Copyright (c) 2015 Tomas Balyo, Karlsruhe Institute of Technology
/*
 * LFQueue.h
 *
 *  Created on: Dec 19, 2014
 *      Author: balyo
 */

#ifndef LFQUEUE_H_
#define LFQUEUE_H_

struct lfds611_queue_state;

class LFQueue {

private:
	lfds611_queue_state* qst;

public:
	/**
	 * each thread except from the creating thread must
	 * call this method before adding or removing data.
	 */
	void registerForUsing();
	void add(void* data);
	bool next(void** data);
	void init(int initialSize);

	LFQueue();
	virtual ~LFQueue();
};

#endif /* LFQUEUE_H_ */
