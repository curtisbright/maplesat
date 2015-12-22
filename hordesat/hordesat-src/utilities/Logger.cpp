// Copyright (c) 2015 Tomas Balyo, Karlsruhe Institute of Technology
/*
 * Logger.cpp
 *
 *  Created on: Mar 9, 2015
 *      Author: balyo
 */

#include "Logger.h"
#include <sys/time.h>
#include <stdio.h>
#include <stdarg.h>

static int verbosityLevelSetting = 0;
static double start = getAbsoluteTime();

double getAbsoluteTime() {
	timeval time;
	gettimeofday(&time, NULL);
	return (double)time.tv_sec + (double)time.tv_usec * .000001;
}

double getTime() {
	return getAbsoluteTime() - start;
}

void setVerbosityLevel(int level) {
	verbosityLevelSetting = level;
}

void log(int verbosityLevel, const char* fmt ...) {
	if (verbosityLevel <= verbosityLevelSetting) {
		va_list args;
		va_start(args, fmt);
		printf("[%.2f] ", getTime());
		vprintf(fmt, args);
		va_end(args);
	}
}




