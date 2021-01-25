/*
 * queue.cpp -- queue example implemented using pmemobj cpp bindings
 *
 * Please see pmem.io blog posts for more details.
 */

#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <libpmemobj++/make_persistent.hpp>
#include <libpmemobj++/p.hpp>
#include <libpmemobj++/persistent_ptr.hpp>
#include <libpmemobj++/pool.hpp>
#include <libpmemobj++/transaction.hpp>
#include <stdexcept>
#include <string>
#include <sys/stat.h>
#include <unistd.h>
#include <thread>
#include <chrono>
#include <algorithm>
#include <fstream>
#include <mutex>

#define LAYOUT "queue"
#define N 80 // number of processes
#define MILLION  1000000LL

//#define RANDOP true

#define MAX_POOL_SIZE 4000  // number of nodes in the pool
// #define MAX_POOL_SIZE 80  // number of nodes in the pool
#define ACK -1
#define EMPTY -2
#define NONE -3
#define PUSH_OP 1
#define POP_OP 0
#define SIZE 10000

// Macros needed for persistence
#ifdef PWB_IS_CLFLUSH_PFENCE_NOP
/*
   * More info at http://elixir.free-electrons.com/linux/latest/source/arch/x86/include/asm/special_insns.h#L213
   * Intel programming manual at https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-optimization-manual.pdf
   * Use these for Broadwell CPUs (cervino server)
   */
  #define PWB(addr)              __asm__ volatile("clflush (%0)" :: "r" (addr) : "memory")                      // Broadwell only works with this.
  #define PFENCE()               {}                                                                             // No ordering fences needed for CLFLUSH (section 7.4.6 of Intel manual)
  #define PSYNC()                {}
  #define PPWB(addr)              __asm__ volatile("clflush (%0)" :: "r" (addr) : "memory")  // parallel PWB
  #define PPFENCE()               {} // parallel PFENCE
#elif PWB_IS_CLFLUSH
#define PWB(addr)              __asm__ volatile("clflush (%0)" :: "r" (addr) : "memory")
  #define PFENCE()               __asm__ volatile("sfence" : : : "memory")
  #define PSYNC()                __asm__ volatile("sfence" : : : "memory")
  #define PPWB(addr)              __asm__ volatile("clflush (%0)" :: "r" (addr) : "memory") // parallel PWB
  #define PPFENCE()               __asm__ volatile("sfence" : : : "memory") // parallel PFENCE
#elif PWB_IS_CLWB
/* Use this for CPUs that support clwb, such as the SkyLake SP series (c5 compute intensive instances in AWS are an example of it) */
  #define PWB(addr)              __asm__ volatile(".byte 0x66; xsaveopt %0" : "+m" (*(volatile char *)(addr)))  // clwb() only for Ice Lake onwards
  #define PFENCE()               __asm__ volatile("sfence" : : : "memory")
  #define PSYNC()                __asm__ volatile("sfence" : : : "memory")
  #define PPWB(addr)              __asm__ volatile(".byte 0x66; xsaveopt %0" : "+m" (*(volatile char *)(addr))) // parallel PWB
  #define PPFENCE()               __asm__ volatile("sfence" : : : "memory") // parallel PFENCE
#elif PWB_IS_NOP
/* pwbs are not needed for shared memory persistency (i.e. persistency across process failure) */
  #define PWB(addr)              {}
  #define PFENCE()               __asm__ volatile("sfence" : : : "memory")
  #define PSYNC()                __asm__ volatile("sfence" : : : "memory")
  #define PPWB(addr)              {} // parallel PWB
  #define PPFENCE()               __asm__ volatile("sfence" : : : "memory") // parallel PFENCE
#elif PWB_IS_CLFLUSHOPT
/* Use this for CPUs that support clflushopt, which is most recent x86 */
  #define PWB(addr)              __asm__ volatile(".byte 0x66; clflush %0" : "+m" (*(volatile char *)(addr)))    // clflushopt (Kaby Lake)
  #define PFENCE()               __asm__ volatile("sfence" : : : "memory")
  #define PSYNC()                __asm__ volatile("sfence" : : : "memory")
  #define PPWB(addr)             __asm__ volatile(".byte 0x66; clflush %0" : "+m" (*(volatile char *)(addr))) // parallel PWB
  #define PPFENCE()              __asm__ volatile("sfence" : : : "memory") // parallel PFENCE
#elif PWB_IS_PMEM
#define PWB(addr)              pmem_flush(addr, sizeof(addr))
  #define PFENCE()               pmem_drain()
  #define PSYNC() 				 {}
  #define PPWB(addr)              pmem_flush(addr, sizeof(addr)) // parallel PWB
  #define PPFENCE()               pmem_drain() // parallel PFENCE
#elif COUNT_PWB
#define PWB(addr)              __asm__ volatile("clflush (%0)" :: "r" (addr) : "memory") ; localPwbCounter++
#define PFENCE()               __asm__ volatile("sfence" : : : "memory") ; localPfenceCounter++
#define PSYNC()                __asm__ volatile("sfence" : : : "memory")
#define PPWB(addr)              __asm__ volatile("clflush (%0)" :: "r" (addr) : "memory") ; localParallelPwbCounter++
#define PPFENCE()               __asm__ volatile("sfence" : : : "memory") ; localParallelPfenceCounter++
#else
#error "You must define what PWB is. Choose PWB_IS_CLFLUSHOPT if you don't know what your CPU is capable of"
#endif


using namespace std::chrono;

std::atomic<bool> cLock {false};    // holds true when locked, holds false when unlocked
std::atomic<int> gRecoveryLock {0}; // holds 1 when locked, holds 0 when unlocked, holds 2 when it was locked once
std::mutex pLock; // Used to add local PWB and PFENCE instructions count to the global variables

thread_local int localPwbCounter = 0;
thread_local int localPfenceCounter = 0;
int pwbCounter = 0;
int pfenceCounter = 0;

thread_local int localParallelPwbCounter = 0;
thread_local int localParallelPfenceCounter = 0;
int pwbParallelCounter = 0;
int pfenceParallelCounter = 0;

thread_local int l_combining_counter = 0;
int combining_counter = 0;

double r_max_stack_size = 0;
double r_stack_size_on_combine = 0;

double max_stack_size = 0;
double stack_size_on_combine = 0;

int pushList[N];
int popList[N];
short collectedValid[N];

int NN = N;  // number of processes running now
const int num_words = MAX_POOL_SIZE / 64 + 1;
uint64_t free_nodes_log [num_words];

uint64_t free_nodes_log_h1;

namespace
{

/* available queue operations */
    enum queue_op {
        UNKNOWN_QUEUE_OP,
        QUEUE_PUSH,
        QUEUE_POP,
        QUEUE_SHOW,

        MAX_QUEUE_OP,
    };

/* queue operations strings */
    const char *ops_str[MAX_QUEUE_OP] = {"", "push", "pop", "show"};

/*
 * parse_queue_op -- parses the operation string and returns matching queue_op
 */
    queue_op
    parse_queue_op(const char *str)
    {
        for (int i = 0; i < MAX_QUEUE_OP; ++i)
            if (strcmp(str, ops_str[i]) == 0)
                return (queue_op)i;

        return UNKNOWN_QUEUE_OP;
    }
}

using pmem::obj::delete_persistent;
using pmem::obj::make_persistent;
using pmem::obj::p;
using pmem::obj::persistent_ptr;
using pmem::obj::pool;
using pmem::obj::pool_base;
using pmem::obj::transaction;

namespace examples
{

    struct stack_data {
        p<int64_t> top;
        p<int64_t> data[SIZE];
    };

/*
 * Persistent memory list-based queue
 *
 * A simple, not template based, implementation of queue using
 * libpmemobj C++ API. It demonstrates the basic features of persistent_ptr<>
 * and p<> classes.
 */
    class pmem_stack {

    public:
        /*
         * Inserts a new element at the end of the queue.
         */

        // Check if the queue is full
        bool isFull() {
            if (s->top == SIZE) {
                return true;
            }
            return false;
        }
        // Check if the queue is empty
        bool isEmpty() {
            if (s->top == -1)
                return true;
            else
                return false;
        }

        void
        push(uint64_t value)
        {
            std::lock_guard<std::mutex>guard(*mutex);
            if (isFull()) {
                std::cout << "Stack is full";
            } else {
                s->data[s->top + 1] = value;
                PWB(&s->data[s->top + 1]);
                s->top = s->top + 1;
                PWB(&s->top);
                PFENCE();
                //std::cout << std::endl << "Inserted " << element << std::endl;
            }
            r_stack_size_on_combine += s->top + 1.0;
            r_max_stack_size = std::max(double(s->top)+1, r_max_stack_size);
        }

        /*
         * Removes the first element in the queue.
         */
        uint64_t
        pop()
        {
            std::lock_guard<std::mutex>guard(*mutex);
            int element;
            if (isEmpty()) {
                r_stack_size_on_combine += std::max(double(s->top)+1, 0.0);
                //std::cout << "Stack is empty" << std::endl;
                return (-1);
            } else {
                element = s->data[s->top];
                s->top = s->top - 1;
                PWB(&s->top);
                PFENCE();
                r_stack_size_on_combine += std::max(double(s->top)+1, 0.0);
                return (element);
            }
        }

        /*
         * Prints the entire contents of the queue.
         */
//        void
//        show(void) const
//        {
//            for (auto n = head; n != nullptr; n = n->next)
//                std::cout << n->value << std::endl;
//        }

        pmem_stack(pool<examples::stack_data>& pool_base, persistent_ptr<stack_data> data)  : p(pool_base), s(data) {
            transaction::run(p, [&] {
                s = make_persistent<stack_data>();
                s->top = -1;
            });
            mutex = std::make_shared<std::mutex>();
        }

        pmem_stack() = default;

        pmem_stack& operator=(const pmem_stack&) = default;

//        ~pmem_stack() {
//            transaction::run(p, [&] {
//                delete_persistent<stack_data>(s);
//            });
//        }

    private:
        pool<examples::stack_data> p;
        persistent_ptr<stack_data> s;
        std::shared_ptr<std::mutex> mutex;

    };

} /* namespace examples */



static inline int
file_exists(char const *file)
{
    return access(file, 0);
}

std::tuple<uint64_t, double, double, double, double, double, double, double> pushPopTest(int numThreads, const long numPairs, const int numRuns, const int numSameOps) {
    const uint64_t kNumElements = 0; // Number of initial items in the stack
    static const long long NSEC_IN_SEC = 1000000000LL;

    pool<examples::stack_data> p;
    examples::pmem_stack q;
//    auto p = pool<examples::stack_data>::create("/mnt/ram/data", LAYOUT, PMEMOBJ_MIN_POOL, (S_IWUSR | S_IRUSR));
//    examples::pmem_stack s(p, p.root());
    //persistent_ptr<examples::pmem_stack> s(p.root());

    size_t params [N];
    size_t ops [N];
    std::thread threads_pool[N];

    std::cout << "in push pop" << std::endl;
    nanoseconds deltas[numThreads][numRuns];
    std::atomic<bool> startFlag = { false };

    std::cout << "##### " << "Detectable Flat Combining" << " #####  \n";

    auto pushpop_lambda = [&numThreads, &startFlag,&numPairs, &q, &p](nanoseconds *delta, const int tid) {
        size_t param = tid;
        while (!startFlag.load()) {} // Spin until the startFlag is set
        // Measurement phase
        auto startBeats = steady_clock::now();
        for (long long iter = 0; iter < numPairs/numThreads; iter++) {
            q.push(6);
            if (q.pop() != 6) std::cout << "Error at measurement pop() iter=" << iter << "\n";
        }
        auto stopBeats = steady_clock::now();
        *delta = stopBeats - startBeats;
        std::lock_guard<std::mutex> lock(pLock);
        pwbCounter += localPwbCounter;
        pfenceCounter += localPfenceCounter;
        pwbParallelCounter += localParallelPwbCounter;
        pfenceParallelCounter += localParallelPfenceCounter;
        combining_counter += l_combining_counter;
        max_stack_size += double(r_max_stack_size) / double(numThreads);
        stack_size_on_combine += r_stack_size_on_combine / (double(numPairs)*2.0*numThreads);
    };

    auto pushpop_k_lambda = [&numThreads, &startFlag,&numPairs, &numSameOps, &q, &p](nanoseconds *delta, const int tid) {
        //UserData* ud = new UserData{0,0};
        size_t param = tid;
        while (!startFlag.load()) {} // Spin until the startFlag is set
        // Measurement phase
        auto startBeats = steady_clock::now();
        for (long long iter = 0; iter < numPairs/(numThreads*numSameOps); iter++) {
            for (long iter_s = 0; iter_s < numSameOps; iter_s++) {
                q.push(param);
            }
            for (long iter_s = 0; iter_s < numSameOps; iter_s++) {
                q.push(param);
            }
        }
        auto stopBeats = steady_clock::now();
        *delta = stopBeats - startBeats;
        std::lock_guard<std::mutex> lock(pLock);
        pwbCounter += localPwbCounter;
        pfenceCounter += localPfenceCounter;
        pwbParallelCounter += localParallelPwbCounter;
        pfenceParallelCounter += localParallelPfenceCounter;
        combining_counter += l_combining_counter;
    };

    auto randop_lambda = [&numThreads, &startFlag,&numPairs, &q, &p](nanoseconds *delta, const int tid) {
        size_t param = tid;
        while (!startFlag.load()) {} // Spin until the startFlag is set
        // Measurement phase
        // thread_local int operations[2 * numPairs/numThreads];
        auto startBeats = steady_clock::now();
        for (long long iter = 0; iter < 2 * numPairs/numThreads; iter++) {
            int randop = rand() % 2;         // randop in the range 0 to 1
            if (randop == 0) {
                q.push(param);
            }
            else if (randop == 1) {
                q.pop();
            }
        }
        auto stopBeats = steady_clock::now();
        *delta = stopBeats - startBeats;
        std::lock_guard<std::mutex> lock(pLock);
        pwbCounter += localPwbCounter;
        pfenceCounter += localPfenceCounter;
        pwbParallelCounter += localParallelPwbCounter;
        pfenceParallelCounter += localParallelPfenceCounter;
        combining_counter += l_combining_counter;
    };

    for (int irun = 0; irun < numRuns; irun++) {
        NN = numThreads;
        r_stack_size_on_combine = 0;
        r_max_stack_size = 0;

//        p = pool<examples::pmem_stack>::create("/mnt/ram/data", LAYOUT, PMEMOBJ_MIN_POOL, (S_IWUSR | S_IRUSR));
//        s = p.root();
//        transaction_allocations(s, p);
        p = pool<examples::stack_data>::create("/mnt/ram/data", LAYOUT, PMEMOBJ_MIN_POOL, (S_IWUSR | S_IRUSR));
        q = examples::pmem_stack(p, p.root());
        std::cout << "Finished allocating!" << std::endl;

        // Fill the queue with an initial amount of nodes
        size_t param = size_t(41);
        for (uint64_t ielem = 0; ielem < kNumElements; ielem++) {
            q.push(param);
        }

        std::thread enqdeqThreads[numThreads];
#ifdef SAME100_BENCH
        // for (int tid = 0; tid < numThreads; tid++) enqdeqThreads[tid] = std::thread(randop_lambda, &deltas[tid][irun], tid);
		for (int tid = 0; tid < numThreads; tid++) enqdeqThreads[tid] = std::thread(pushpop_k_lambda, &deltas[tid][irun], tid);
#elif defined RANDOP
        for (int tid = 0; tid < numThreads; tid++) enqdeqThreads[tid] = std::thread(randop_lambda, &deltas[tid][irun], tid);
#else
        for (int tid = 0; tid < numThreads; tid++) enqdeqThreads[tid] = std::thread(pushpop_lambda, &deltas[tid][irun], tid);
#endif
        startFlag.store(true);
        // Sleep for 2 seconds just to let the threads see the startFlag
        std::this_thread::sleep_for(2s);
        for (int tid = 0; tid < numThreads; tid++) enqdeqThreads[tid].join();
        startFlag.store(false);

        //transaction_deallocations(proot, pop);
        /* Cleanup */
        /* Close persistent pool */
        p.close ();
        std::remove("/mnt/ram/data");
    }

    // Sum up all the time deltas of all threads so we can find the median run
    std::vector<nanoseconds> agg(numRuns);
    for (int irun = 0; irun < numRuns; irun++) {
        agg[irun] = 0ns;
        for (int tid = 0; tid < numThreads; tid++) {
            agg[irun] += deltas[tid][irun];
        }
    }

    // Compute the median. numRuns should be an odd number
    std::sort(agg.begin(),agg.end());
    auto median = agg[numRuns/2].count()/numThreads; // Normalize back to per-thread time (mean of time for this run)

    std::cout << "Total Ops/sec = " << numPairs*2*NSEC_IN_SEC/median << "\n";
    // std::cout << "combining_counter: " << combining_counter << std::endl;
#if defined(COUNT_PWB)
    double pwbPerOp = double(pwbCounter) / double(numPairs*2);
    double pfencePerOp = double(pfenceCounter) / double(numPairs*2);
    double pwbParallelPerOp = double(pwbParallelCounter) / double(numPairs*2);
    double pfenceParallelPerOp = double(pfenceParallelCounter) / double(numPairs*2);
    double combiningPerOp = double(combining_counter) / double(numPairs*2);
    double average_stack_size = double(stack_size_on_combine) / numRuns;
    double final_max = double(max_stack_size) / numRuns;
    std::cout << "#pwb/#op: " << std::fixed << pwbPerOp;
    std::cout << ", #pfence/#op: " << std::fixed << pfencePerOp;
    std::cout << ", T #pwb/#op: " << std::fixed << pwbPerOp + pwbParallelPerOp;
    std::cout << ", T #pfence/#op: " << std::fixed << pfencePerOp + pfenceParallelPerOp;
    std::cout << ", #combining/#op: " << std::fixed << combiningPerOp;
    std::cout << ", max stack size: " << std::fixed << final_max;
    std::cout << ", average stack size: " << std::fixed << average_stack_size << std::endl;
    // std::cout << ", Total #pwb/#op (parallel PWBs included): " << std::fixed << pwbPerOp + pwbParallelPerOp;
    // std::cout << "#Total pfence/#op (parallel PFENCEs included): " << std::fixed << pfencePerOp + pfenceParallelPerOp << std::endl;

    combining_counter = 0;
    l_combining_counter = 0;
    pwbCounter = 0; pfenceCounter = 0; pwbParallelCounter = 0; pfenceParallelCounter = 0;
    localPwbCounter = 0; localPfenceCounter = 0; localParallelPwbCounter = 0; localParallelPfenceCounter = 0;
    max_stack_size = 0; stack_size_on_combine = 0;
    return std::make_tuple(numPairs*2*NSEC_IN_SEC/median, pwbPerOp, pfencePerOp, pwbPerOp + pwbParallelPerOp, pfencePerOp + pfenceParallelPerOp, combiningPerOp, final_max, average_stack_size);
#endif
    return std::make_tuple(numPairs*2*NSEC_IN_SEC/median, 0, 0, 0, 0, 0, 0, 0);
}

int runSeveralTests() {
    const std::string dataFilename { "log" };
    const std::string pdataFilename { "report" };
    std::vector<int> threadList = { 1, 2, 4, 8, 10, 16, 24, 32, 40 };     // For Castor
    // std::vector<int> threadList = { 1, 2, 4, 8, 10, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40};     // For Castor
    // std::vector<int> threadList = { 1, 2, 4, 8, 10, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 64, 68, 72, 76, 80 };     // For Castor
    const int numRuns = 10;                                           // Number of runs
    // const int numRuns = 1;                                           // Number of runs
    const long numPairs = 1*MILLION;                                 // 1M is fast enough on the laptop
    const int numSameOps = 100;

    std::tuple<uint64_t, double, double, double, double, double, double, double> results[threadList.size()];
    std::string cName = "DFC";
    // Reset results
    std::memset(results, 0, sizeof(uint64_t)*threadList.size());

    // Enq-Deq Throughput benchmarks
    for (int it = 0; it < threadList.size(); it++) {
        int nThreads = threadList[it];
        std::cout << "\n----- pstack-ll (push-pop)   threads=" << nThreads << "   pairs=" << numPairs/MILLION << "M   runs=" << numRuns << " -----\n";
        results[it] = pushPopTest(nThreads, numPairs, numRuns, numSameOps);
    }

#if not defined(COUNT_PWB)
    // Export tab-separated values to a file to be imported in gnuplot or excel
    std::ofstream dataFile;
    dataFile.open(dataFilename);
    dataFile << "Threads\t";
    // Printf class names for each column
    dataFile << cName << "\t";
    dataFile << "\n";
    for (int it = 0; it < threadList.size(); it++) {
        dataFile << threadList[it] << "\t";
        dataFile << std::get<0>(results[it]) << "\t";
        dataFile << "\n";
    }
    dataFile.close();
    std::cout << "\nSuccessfuly saved results in " << dataFilename << "\n";
#endif

#if defined(COUNT_PWB)
    // Export tab-separated values to a file to be imported in gnuplot or excel
    std::ofstream pdataFile;
    pdataFile.open(pdataFilename);
    pdataFile << "Threads\t";
    // Printf class names for each column
    pdataFile << "OPS/Sec\t" << "DFC-PWB" << "\t" << "DFC-PFENCE" << "\t" << "DFC-PWB-T" << "\t" << "DFC-PFENCE-T" << "\t" << "DFC-COMBINING" << "\t" << "MAX-SIZE" << "\t" << "AVG-SIZE" << "\t";
    pdataFile << "\n";
    for (int it = 0; it < threadList.size(); it++) {
        pdataFile << threadList[it] << "\t";
        pdataFile << std::get<0>(results[it]) << "\t";
        pdataFile << std::get<1>(results[it]) << "\t";
        pdataFile << std::get<2>(results[it]) << "\t";
        pdataFile << std::get<3>(results[it]) << "\t";
        pdataFile << std::get<4>(results[it]) << "\t";
        pdataFile << std::get<5>(results[it]) << "\t";
        pdataFile << std::get<6>(results[it]) << "\t";
        pdataFile << std::get<7>(results[it]) << "\t";
        pdataFile << "\n";
    }
    pdataFile.close();
    std::cout << "\nSuccessfuly saved results in " << pdataFilename << "\n";
#endif

    return 0;
}


int main(int argc, char *argv[]) {
    runSeveralTests();
    return 0;
}

int old_main(int argc, char *argv[])
{
    if (argc < 3) {
        std::cerr << "usage: " << argv[0]
                  << " file-name [push [value]|pop|show]" << std::endl;
        return 1;
    }

    const char *path = argv[1];

    queue_op op = parse_queue_op(argv[2]);

    pool<examples::pmem_stack> pop;
    persistent_ptr<examples::pmem_stack> q(pop.root());

    try {
        if (file_exists(path) != 0) {
            pop = pool<examples::pmem_stack>::create(
                    path, LAYOUT, PMEMOBJ_MIN_POOL, (S_IWUSR | S_IRUSR));
        } else {
            pop = pool<examples::pmem_stack>::open(path, LAYOUT);
        }
        q = pop.root();
    } catch (const pmem::pool_error &e) {
        std::cerr << "Exception: " << e.what() << std::endl;
        return 1;
    } catch (const pmem::transaction_error &e) {
        std::cerr << "Exception: " << e.what() << std::endl;
        return 1;
    }

    switch (op) {
        case QUEUE_PUSH:
            try {
                q->push(std::stoull(argv[3]));
            } catch (const std::runtime_error &e) {
                std::cerr << "Exception: " << e.what()
                          << std::endl;
                return 1;
            }
            break;
        case QUEUE_POP:
            try {
                std::cout << q->pop() << std::endl;
            } catch (const std::runtime_error &e) {
                std::cerr << "Exception: " << e.what()
                          << std::endl;
                return 1;
            } catch (const std::logic_error &e) {
                std::cerr << "Exception: " << e.what()
                          << std::endl;
                return 1;
            }
            break;
        case QUEUE_SHOW:
            //s->show();
            break;
        default:
            std::cerr << "Invalid queue operation" << std::endl;
            return 1;
    }

    try {
        pop.close();
    } catch (const std::logic_error &e) {
        std::cerr << "Exception: " << e.what() << std::endl;
        return 1;
    }
    return 0;
}