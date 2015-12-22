// Copyright (c) 2015 Tomas Balyo, Karlsruhe Institute of Technology
/*
 * Logger.h
 *
 *  Created on: Mar 9, 2015
 *      Author: balyo
 */

#ifndef LOGGER_H_
#define LOGGER_H_

double getTime();
double getAbsoluteTime();
void setVerbosityLevel(int level);
void log(int verbosityLevel, const char* fmt ...);


#endif /* LOGGER_H_ */
