// Copyright (c) 2015 Tomas Balyo, Karlsruhe Institute of Technology
//============================================================================
// Name        : hordesat.cpp
// Author      : Tomas Balyo
// Version     : $Revision: 46 $
// Date        : $Date: 2015-04-09 16:14:19 +0200 (Thu, 09 Apr 2015) $
// Copyright   : copyright KIT
//============================================================================

#include "solvers/MiniSat.h"
#include "solvers/Lingeling.h"
#include "utilities/DebugUtils.h"
#include "utilities/Threading.h"
#include "utilities/ParameterProcessor.h"
#include "sharing/AllToAllSharingManager.h"
#include "sharing/LogSharingManager.h"

#include <stdio.h>
#include <stdlib.h>
#include <mpi.h>
#include <algorithm>
#include <csignal>
#include <unistd.h>
#include "utilities/Logger.h"


ParameterProcessor params;
vector<PortfolioSolverInterface*> solvers;
int solversCount = 0;
bool solvingDoneLocal = false;
SatResult finalResult = UNKNOWN;
Mutex interruptLock;

SharingManagerInterface* sharingManager = NULL;

// =========================
// end detection
// =========================
#define SOLVING_DONE -10
int* endingBuffer = NULL;

void initializeEndingDetection(int mpi_size) {
	endingBuffer = new int[mpi_size];
}

void stopAllSolvers() {
	interruptLock.lock();
	solvingDoneLocal = true;
	for (int i = 0; i < solversCount; i++) {
		solvers[i]->setSolverInterrupt();
	}
	interruptLock.unlock();
}

// Return true if the solver should stop.
bool getGlobalEnding(int mpi_size, int mpi_rank) {
	int sendMsg = 0;
	if (solvingDoneLocal) {
		sendMsg = SOLVING_DONE;
	}
	MPI_Allgather(&sendMsg, 1, MPI_INT, endingBuffer, 1, MPI_INT, MPI_COMM_WORLD);
	for (int r = 0; r < mpi_size; r++) {
		if (endingBuffer[r] == SOLVING_DONE) {
			stopAllSolvers();
			return true;
		}
	}
	return false;
}

void* solverRunningThread(void* arg) {
	PortfolioSolverInterface* solver = (PortfolioSolverInterface*)arg;
	while (true) {
		interruptLock.lock();
		if (solvingDoneLocal) {
			interruptLock.unlock();
			break;
		} else {
			solver->unsetSolverInterrupt();
		}
		interruptLock.unlock();
		SatResult res = solver->solve();
		if (res == SAT) {
			solvingDoneLocal = true;
			finalResult = SAT;
		}
		if (res == UNSAT) {
			solvingDoneLocal = true;
			finalResult = UNSAT;
		}
	}
	return NULL;
}

void sparseDiversification(int mpi_size, int mpi_rank) {
	int totalSolvers = mpi_size * solversCount;
    int vars = solvers[0]->getVariablesCount();
    for (int sid = 0; sid < solversCount; sid++) {
    	int shift = (mpi_rank * solversCount) + sid;
		for (int var = 1; var + totalSolvers < vars; var += totalSolvers) {
			solvers[sid]->setPhase(var + shift, true);
		}
    }
}

void randomDiversification(unsigned int seed) {
	srand(seed);
    int vars = solvers[0]->getVariablesCount();
    for (int sid = 0; sid < solversCount; sid++) {
		for (int var = 1; var <= vars; var++) {
			solvers[sid]->setPhase(var, rand()%2 == 1);
		}
    }
}

void sparseRandomDiversification(unsigned int seed, int mpi_size) {
	srand(seed);
	int totalSolvers = solversCount * mpi_size;
    int vars = solvers[0]->getVariablesCount();
    for (int sid = 0; sid < solversCount; sid++) {
		for (int var = 1; var <= vars; var++) {
			if (rand() % totalSolvers == 0) {
				solvers[sid]->setPhase(var, rand() % 2 == 1);
			}
		}
    }
}

void nativeDiversification(int mpi_rank, int mpi_size) {
	int base = mpi_rank * solversCount;
    for (int sid = 0; sid < solversCount; sid++) {
    	solvers[sid]->diversify(sid + base, mpi_size * solversCount);
    }
}

void binValueDiversification(int mpi_size, int mpi_rank) {
	int totalSolvers = mpi_size * solversCount;
	int tmp = totalSolvers;
	int log = 0;
	while (tmp) {
		tmp >>= 1;
		log++;
	}
    int vars = solvers[0]->getVariablesCount();
    for (int sid = 0; sid < solversCount; sid++) {
    	int num = mpi_rank * sid;
		for (int var = 1; var < vars; var++) {
			int bit = var % log;
			bool phase = (num >> bit) & 1 ? true : false;
			solvers[sid]->setPhase(var, phase);
		}
    }
}

int main(int argc, char** argv) {
	MPI_Init(&argc, &argv);

	params.init(argc, argv);

	if (params.getFilename() == NULL || params.isSet("h")) {
		puts("This is HordeSat ($Revision: 46 $)");
		puts("USAGE: [mpirun ...] ./hordesat [parameters] input.cnf");
		puts("Parameters:");
		puts("        -d=0...7\t diversification 0=none, 1=sparse, 2=dense, 3=random, 4=native(plingeling), 5=1&4, 6=sparse-random, 7=6&4, default is 1.");
		puts("        -e=0,1,2\t clause exchange mode 0=none, 1=all-to-all, 2=log-partners, default is 1.");
		puts("        -fd\t\t filter duplicate clauses.");
		puts("        -c=<INT>\t use that many cores on each mpi node, default is 1.");
		puts("        -v=<INT>\t verbosity level, higher means more messages, default is 1.");
		puts("        -s=minisat\t use minisat instead of lingeling");
		puts("        -s=combo\t use both minisat and lingeling");
		puts("        -r=<INT>\t max number of rounds (~timelimit in seconds), default is unlimited.");
		puts("        -i=<INT>\t communication interval in miliseconds, default is 1000.");
		puts("        -t=<INT>\t timelimit in seconds, default is unlimited.");
		MPI_Finalize();
		return 0;
	}

	int mpi_size, mpi_rank;
	MPI_Comm_size(MPI_COMM_WORLD, &mpi_size);
	MPI_Comm_rank(MPI_COMM_WORLD, &mpi_rank);

	setVerbosityLevel(params.getIntParam("v", 0));
	if (mpi_rank == 0) {
		setVerbosityLevel(3);
	}

	char hostname[1024];
	gethostname(hostname, 1024);
	log(0, "Running HordeSat ($Revision: 46 $) on %s rank %d/%d input %s with parameters: ",
			hostname, mpi_rank, mpi_size, params.getFilename());
	params.printParams();

	solversCount = params.getIntParam("c", 1);

	for (int i = 0; i < solversCount; i++) {
		if (params.getParam("s") == "minisat") {
			solvers.push_back(new MiniSat());
			log(1, "Running MiniSat on core %d of node %d/%d\n", i, mpi_rank, mpi_size);
		} else if (params.getParam("s") == "combo") {
			if ((mpi_rank + i) % 2 == 0) {
				solvers.push_back(new MiniSat());
				log(1, "Running MiniSat on core %d of node %d/%d\n", i, mpi_rank, mpi_size);
			} else {
				solvers.push_back(new Lingeling());
				log(1, "Running Lingeling on core %d of node %d/%d\n", i, mpi_rank, mpi_size);
			}
		} else {
			solvers.push_back(new Lingeling());
			log(1, "Running Lingeling on core %d of node %d/%d\n", i, mpi_rank, mpi_size);
		}
	}

	loadFormulaToSolvers(solvers, params.getFilename());

	int exchangeMode = params.getIntParam("e", 1);
	if (exchangeMode == 0) {
		log(1, "Clause sharing disabled.\n");
	} else if (mpi_size > 1 || solversCount > 1) {
		switch (exchangeMode) {
		case 1:
			sharingManager = new AllToAllSharingManager(mpi_size, mpi_rank, solvers, params);
			log(1, "Initialized all-to-all clause sharing.\n");
			break;
		case 2:
			sharingManager = new LogSharingManager(mpi_size, mpi_rank, solvers, params);
			log(1, "Initialized log-partners clause sharing.\n");
			break;
		}
	}

	int diversification = params.getIntParam("d", 1);
	switch (diversification) {
	case 1:
		sparseDiversification(mpi_size, mpi_rank);
		log(1, "doing sparse diversification\n");
		break;
	case 2:
		binValueDiversification(mpi_size, mpi_rank);
		log(1, "doing binary value based diversification\n");
		break;
	case 3:
		randomDiversification(2015);
		log(1, "doing random diversification\n");
		break;
	case 4:
		nativeDiversification(mpi_rank, mpi_size);
		log(1, "doing native diversification (plingeling)\n");
		break;
	case 5:
		sparseDiversification(mpi_size, mpi_rank);
		nativeDiversification(mpi_rank, mpi_size);
		log(1, "doing sparse + native diversification (plingeling)\n");
		break;
	case 6:
		sparseRandomDiversification(mpi_rank, mpi_size);
		log(1, "doing sparse random diversification\n");
		break;
	case 7:
		sparseRandomDiversification(mpi_rank, mpi_size);
		nativeDiversification(mpi_rank, mpi_size);
		log(1, "doing random sparse + native diversification (plingeling)\n");
		break;
	case 0:
		log(1, "no diversification\n");
		break;
	}

	initializeEndingDetection(mpi_size);

	Thread** solverThreads = (Thread**) malloc (solversCount*sizeof(Thread*));
	for (int i = 0; i < solversCount; i++) {
		solverThreads[i] = new Thread(solverRunningThread, solvers[i]);
	}

	double startSolving = getTime();
	log(1, "Node %d started its solvers, initialization took %.2f seconds.\n", mpi_rank, startSolving);

	int maxSeconds = params.getIntParam("t", 0);
	int maxRounds = params.getIntParam("r", -1);
	size_t sleepInt = 1000 * params.getIntParam("i", 1000);
	int round = 1;

	while (!getGlobalEnding(mpi_size, mpi_rank)) {
		usleep(sleepInt);
		double timeNow = getTime();
		log(2, "Node %d entering round %d (%.2f seconds solving, %.2f rounds/sec)\n", mpi_rank, round,
			timeNow - startSolving, round/(timeNow - startSolving));
		if (sharingManager != NULL) {
			sharingManager->doSharing();
		}
		if (round == maxRounds || (maxSeconds != 0 && timeNow > maxSeconds)) {
			solvingDoneLocal = true;
		}
		fflush(stdout);
		round++;
	}
	double searchTime = getTime() - startSolving;
	log(0, "node %d finished, joining solver threads\n", mpi_rank);
	for (int i = 0; i < solversCount; i++) {
		solverThreads[i]->join();
	}

	// Statistics gathering
	// Local statistics
	SolvingStatistics locSolveStats;
	for (int i = 0; i < solversCount; i++) {
		SolvingStatistics st = solvers[i]->getStatistics();
		log(1, "thread-stats node:%d/%d thread:%d/%d props:%lu decs:%lu confs:%lu mem:%0.2f\n",
				mpi_rank, mpi_size, i, solversCount, st.propagations, st.decisions, st.conflicts, st.memPeak);
		locSolveStats.conflicts += st.conflicts;
		locSolveStats.decisions += st.decisions;
		locSolveStats.memPeak += st.memPeak;
		locSolveStats.propagations += st.propagations;
		locSolveStats.restarts += st.restarts;
	}
	SharingStatistics locShareStats;
	if (sharingManager != NULL) {
		locShareStats = sharingManager->getStatistics();
	}
	log(1, "node-stats node:%d/%d solved:%d res:%d props:%lu decs:%lu confs:%lu mem:%0.2f shared:%lu filtered:%lu\n",
			mpi_rank, mpi_size, finalResult != 0, finalResult, locSolveStats.propagations, locSolveStats.decisions,
			locSolveStats.conflicts, locSolveStats.memPeak, locShareStats.sharedClauses, locShareStats.filteredClauses);
	// Global statistics
	SatResult globalResult;
	MPI_Reduce(&finalResult, &globalResult, 1, MPI_INT, MPI_MAX, 0, MPI_COMM_WORLD);
	SolvingStatistics globSolveStats;
	MPI_Reduce(&locSolveStats.propagations, &globSolveStats.propagations, 1, MPI_UNSIGNED_LONG, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&locSolveStats.decisions, &globSolveStats.decisions, 1, MPI_UNSIGNED_LONG, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&locSolveStats.conflicts, &globSolveStats.conflicts, 1, MPI_UNSIGNED_LONG, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&locSolveStats.memPeak, &globSolveStats.memPeak, 1, MPI_DOUBLE, MPI_SUM, 0, MPI_COMM_WORLD);
	SharingStatistics globShareStats;
	MPI_Reduce(&locShareStats.sharedClauses, &globShareStats.sharedClauses, 1, MPI_UNSIGNED_LONG, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&locShareStats.importedClauses, &globShareStats.importedClauses, 1, MPI_UNSIGNED_LONG, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&locShareStats.filteredClauses, &globShareStats.filteredClauses, 1, MPI_UNSIGNED_LONG, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&locShareStats.dropped, &globShareStats.dropped, 1, MPI_UNSIGNED_LONG, MPI_SUM, 0, MPI_COMM_WORLD);

	if (mpi_rank == 0) {
		log(0, "glob-stats nodes:%d threads:%d solved:%d res:%d rounds:%d time:%.2f mem:%0.2f MB props:%.2f decs:%.2f confs:%.2f "
			"shared:%.2f imported:%.2f filtered:%.2f dropped:%.2f\n",
			mpi_size, solversCount, globalResult != 0, globalResult, round,
			searchTime, globSolveStats.memPeak,
			globSolveStats.propagations/searchTime, globSolveStats.decisions/searchTime, globSolveStats.conflicts/searchTime,
			globShareStats.sharedClauses/searchTime, globShareStats.importedClauses/searchTime, globShareStats.filteredClauses/searchTime, globShareStats.dropped/searchTime);
	}

	// Cleanup
	for (int i = 0; i < solversCount; i++) {
		delete solverThreads[i];
	}
	free(solverThreads);
	delete sharingManager;

	MPI_Finalize();
	return 0;
}
