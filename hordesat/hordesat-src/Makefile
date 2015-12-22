WSPACE = 	..

CXXFLAGS =	-O3 -g -Wall -fmessage-length=0 -I$(WSPACE)/minisat -I$(WSPACE)/lingeling -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS

OBJS =		hordesat.o utilities/ClauseFilter.o solvers/MiniSat.o solvers/Lingeling.o utilities/ClauseDatabase.o \
			utilities/SatUtils.o utilities/Logger.o sharing/AllToAllSharingManager.o \
			sharing/LogSharingManager.o

LIBS =		-lz -L$(WSPACE)/minisat/build/release/lib -lminisat -L$(WSPACE)/lingeling/ -llgl

TARGET =	hordesat

CXX = 		mpic++

$(TARGET):	$(OBJS)
	$(CXX) -o $(TARGET) $(OBJS) $(LIBS)

all:	$(TARGET)

clean:
	rm -f $(OBJS) $(TARGET)
