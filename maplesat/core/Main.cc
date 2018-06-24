/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"

using namespace Minisat;

//=================================================================================================


void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %"PRIu64"\n", solver.starts);
    printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
    printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
    printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
    printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        printStats(*solver);
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:


int main(int argc, char** argv)
{
    try {
        setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        // printf("This is MiniSat 2.0 beta\n");
        
#if defined(__linux__) && defined(_FPU_EXTENDED) && defined(_FPU_DOUBLE) && defined(_FPU_GETCW)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
	StringOption assums ("MAIN", "assums", "Comma-separated list of assumptions to use.");
        
        parseOptions(argc, argv, true);

        Solver S;
        double initial_time = cpuTime();

        S.verbosity = verb;
        
        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("WARNING! Could not set resource limit: Virtual memory.\n");
            } }
        
        if (argc == 1)
            printf("Reading from standard input... Use '--help' for help.\n");
        
        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        
        if (S.verbosity > 0){
            printf("============================[ Problem Statistics ]=============================\n");
            printf("|                                                                             |\n"); }
        
        parse_DIMACS(in, S);
        gzclose(in);
        FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;
        
        if (S.verbosity > 0){
            printf("|  Number of variables:  %12d                                         |\n", S.nVars());
            printf("|  Number of clauses:    %12d                                         |\n", S.nClauses()); }
        
        double parsed_time = cpuTime();
        if (S.verbosity > 0){
            printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);
            printf("|                                                                             |\n"); }
 
        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        signal(SIGINT, SIGINT_interrupt);
        signal(SIGXCPU,SIGINT_interrupt);
       
        if (!S.simplify()){
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (S.verbosity > 0){
                printf("===============================================================================\n");
                printf("Solved by unit propagation\n");
                printStats(S);
                printf("\n"); }
            printf("UNSATISFIABLE\n");
            exit(20);
        }
        
        vec<Lit> dummy;
        if (assums) {
            S.starting_points[0] = std::make_pair(0, 0);
            int last_x = 0;
            int last_y = 0;
            int last_i = 1;

            const char* the_assums = assums;
            char* tmp = (char*)the_assums;
            int i;
            while (sscanf(tmp, "%d", &i) == 1) {
                if(i == last_i+1)
                    last_x++;
                else
                    last_y++;
                last_i = i;
                S.m++;
                S.starting_points[S.m] = std::make_pair(last_x, last_y);

                Var v = abs(i) - 1;
                Lit l = i > 0 ? mkLit(v) : ~mkLit(v);
                dummy.push(l);
                while(*tmp != ',' && *tmp != '\0')
                    tmp++;
                if(*tmp == ',')
                    tmp++;
            }
        }
        #ifdef DEBUG
        printf("n: %d k: %d Starting points: ", S.n, S.k);
        for(uint i = 0; i <= S.m; i++) {
            printf("(%d %d) ", S.starting_points[i].first, S.starting_points[i].second);
        }
        printf("\n");
        printf("blocking points: ");
        #endif

        for(uint j=1; j<=S.m; j++)
        {   for(uint i=0; i<j; i++)
            {   const int rise = S.starting_points[j].second - S.starting_points[i].second;
                const int run = S.starting_points[j].first - S.starting_points[i].first;
                if(rise != 0 && run != 0)
                {   const int g = S.gcd(rise, run);
                    const int g2 = S.gcd(abs(S.starting_points[j].second*run-rise*S.starting_points[i].first), run);
                    const int min_run = run/g;
                    const int min_rise = rise/g;
                    const double slope_dbl = (min_rise)/(double)(min_run);
                    const double b = ((S.starting_points[j].second*run - rise*S.starting_points[j].first)/g2)/(double)(run/g2);
                    const line myline = std::make_pair(slope_dbl, b);
                    std::map<line, uint>::iterator search = S.starting_lines.find(myline);
                    if(search == S.starting_lines.end())
                        S.starting_lines.insert(std::make_pair(myline, 1));
                    else
                    {   search->second++;
                        if(search->second == (S.k-1)*(S.k-2)/2)
                        {   uint last_x = S.starting_points[j].first+min_run, last_y = S.starting_points[j].second+min_rise;
                            while(last_x+last_y < S.n)
                            {
                                dummy.push(~mkLit(S.varno(last_x, last_y)));
                                #ifdef DEBUG
                                printf("(%d %d) ", last_x, last_y);
                                #endif
                                last_x += min_run;
                                last_y += min_rise;
                            }
                        }
                        if(search->second == (S.k-2)*(S.k-3)/2)
                        {   uint last_x_1 = S.starting_points[j].first+min_run, last_y_1 = S.starting_points[j].second+min_rise;
                            uint last_x_2 = last_x_1+min_run, last_y_2 = last_y_1+min_rise;
                            while(last_x_1+last_y_1 < S.n)
                            {   while(last_x_2+last_y_2 < S.n)
                                {   
                                    S.addClause(~mkLit(S.varno(last_x_1, last_y_1)), ~mkLit(S.varno(last_x_2, last_y_2)));
                                    #ifdef DEBUG
                                    printf("[(%d %d) (%d %d)] ", last_x_1, last_y_1, last_x_2, last_y_2);
                                    #endif
                                    last_x_2 += min_run;
                                    last_y_2 += min_rise;
                                }
                                last_x_1 += min_run;
                                last_y_1 += min_rise;
                                last_x_2 = last_x_1+min_run;
                                last_y_2 = last_y_1+min_rise;
                            }
                        }
                    }
                }
            }
        }
        #ifdef DEBUG
        printf("\n");
        #endif

        lbool ret = S.solveLimited(dummy);
        if (S.verbosity > 0){
            printStats(S);
            printf("\n"); }
        printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
        if (res != NULL){
            if (ret == l_True){
                fprintf(res, "SAT\n");
                for (int i = 0; i < S.nVars(); i++)
                    if (S.model[i] != l_Undef)
                        fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
                fprintf(res, " 0\n");
            }else if (ret == l_False)
                fprintf(res, "UNSAT\n");
            else
                fprintf(res, "INDET\n");
            fclose(res);
        }
        
#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
