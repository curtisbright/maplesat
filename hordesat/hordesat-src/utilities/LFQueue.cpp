// Copyright (c) 2015 Tomas Balyo, Karlsruhe Institute of Technology
/*
 * LFQueue.cpp
 *
 *  Created on: Dec 19, 2014
 *      Author: balyo
 */

#include "LFQueue.h"

extern "C" {
	#include "../liblfds/inc/liblfds611.h"
}

LFQueue::LFQueue() {
	qst = NULL;
}

void LFQueue::init(int initialSize) {
	lfds611_queue_new(&qst, initialSize);
}

void LFQueue::registerForUsing() {
	lfds611_queue_use(qst);
}

void LFQueue::add(void* data) {
	lfds611_queue_guaranteed_enqueue(qst, data);
}

bool LFQueue::next(void** data) {
	return 1 == lfds611_queue_dequeue(qst, data);
}

LFQueue::~LFQueue() {
	if (qst != NULL) {
		lfds611_queue_delete(qst, NULL, NULL);
	}
}

