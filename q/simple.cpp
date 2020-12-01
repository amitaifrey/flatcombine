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

#define MAX_POOL_SIZE 4000  // number of nodes in the pool
// #define MAX_POOL_SIZE 80  // number of nodes in the pool
#define ACK -1
#define EMPTY -2
#define NONE -3
#define PUSH_OP 1
#define POP_OP 0

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

/*
 * Persistent memory list-based queue
 *
 * A simple, not template based, implementation of queue using
 * libpmemobj C++ API. It demonstrates the basic features of persistent_ptr<>
 * and p<> classes.
 */
    class pmem_queue {

        /* entry in the list */
        struct pmem_entry {
            persistent_ptr<pmem_entry> next;
            p<uint64_t> value;
        };

    public:
        /*
         * Inserts a new element at the end of the queue.
         */
        void
        push(pool_base &pop, uint64_t value)
        {
            std::lock_guard<std::mutex>guard(mutex);
            transaction::run(pop, [&] {
                auto n = make_persistent<pmem_entry>();

                n->value = value;
                n->next = nullptr;

                if (head == nullptr && tail == nullptr) {
                    head = tail = n;
                } else {
                    tail->next = n;
                    tail = n;
                }
            });
        }

        /*
         * Removes the first element in the queue.
         */
        uint64_t
        pop(pool_base &pop)
        {
            std::lock_guard<std::mutex>guard(mutex);
            uint64_t ret = 0;
            transaction::run(pop, [&] {
                if (head == nullptr)
                    transaction::abort(EINVAL);

                ret = head->value;
                auto n = head->next;

                delete_persistent<pmem_entry>(head);
                head = n;

                if (head == nullptr)
                    tail = nullptr;
            });

            return ret;
        }

        /*
         * Prints the entire contents of the queue.
         */
        void
        show(void) const
        {
            for (auto n = head; n != nullptr; n = n->next)
                std::cout << n->value << std::endl;
        }

    private:
        persistent_ptr<pmem_entry> head;
        persistent_ptr<pmem_entry> tail;
        std::mutex mutex;
    };

} /* namespace examples */

static inline int
file_exists(char const *file)
{
    return access(file, 0);
}

std::tuple<uint64_t, double, double, double, double, double> pushPopTest(int numThreads, const long numPairs, const int numRuns, const int numSameOps) {
    const uint64_t kNumElements = 0; // Number of initial items in the stack
    static const long long NSEC_IN_SEC = 1000000000LL;

    pool<examples::pmem_queue> p;
    persistent_ptr<examples::pmem_queue> q;

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
            q->push(p, 6);
            if (q->pop(p) != 6) std::cout << "Error at measurement pop() iter=" << iter << "\n";
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

    auto pushpop_k_lambda = [&numThreads, &startFlag,&numPairs, &numSameOps, &q, &p](nanoseconds *delta, const int tid) {
        //UserData* ud = new UserData{0,0};
        size_t param = tid;
        while (!startFlag.load()) {} // Spin until the startFlag is set
        // Measurement phase
        auto startBeats = steady_clock::now();
        for (long long iter = 0; iter < numPairs/(numThreads*numSameOps); iter++) {
            for (long iter_s = 0; iter_s < numSameOps; iter_s++) {
                q->push(p, param);
            }
            for (long iter_s = 0; iter_s < numSameOps; iter_s++) {
                q->push(p, param);
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
                q->push(p, param);
            }
            else if (randop == 1) {
                q->pop(p);
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

        p = pool<examples::pmem_queue>::create("data", LAYOUT, PMEMOBJ_MIN_POOL, (S_IWUSR | S_IRUSR));
        q = p.root();
//        transaction_allocations(q, p);
        std::cout << "Finished allocating!" << std::endl;

        // Fill the queue with an initial amount of nodes
        size_t param = size_t(41);
        for (uint64_t ielem = 0; ielem < kNumElements; ielem++) {
            q->push(p, param);
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
        std::remove("data");
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
    std::cout << "#pwb/#op: " << std::fixed << pwbPerOp;
    std::cout << ", #pfence/#op: " << std::fixed << pfencePerOp;
    std::cout << ", T #pwb/#op: " << std::fixed << pwbPerOp + pwbParallelPerOp;
    std::cout << ", T #pfence/#op: " << std::fixed << pfencePerOp + pfenceParallelPerOp;
    std::cout << ", #combining/#op: " << std::fixed << combiningPerOp << std::endl;
    // std::cout << ", Total #pwb/#op (parallel PWBs included): " << std::fixed << pwbPerOp + pwbParallelPerOp;
    // std::cout << "#Total pfence/#op (parallel PFENCEs included): " << std::fixed << pfencePerOp + pfenceParallelPerOp << std::endl;

    combining_counter = 0;
    l_combining_counter = 0;
    pwbCounter = 0; pfenceCounter = 0; pwbParallelCounter = 0; pfenceParallelCounter = 0;
    localPwbCounter = 0; localPfenceCounter = 0; localParallelPwbCounter = 0; localParallelPfenceCounter = 0;
    return std::make_tuple(numPairs*2*NSEC_IN_SEC/median, pwbPerOp, pfencePerOp, pwbPerOp + pwbParallelPerOp, pfencePerOp + pfenceParallelPerOp, combiningPerOp);
#endif
    return std::make_tuple(numPairs*2*NSEC_IN_SEC/median, 0, 0, 0, 0, 0);
}

int runSeveralTests() {
    const std::string dataFilename { "log" };
    const std::string pdataFilename { "results" };
    std::vector<int> threadList = { 1, 2, 4, 8, 10, 16, 24, 32, 40 };     // For Castor
    // std::vector<int> threadList = { 1, 2, 4, 8, 10, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40};     // For Castor
    // std::vector<int> threadList = { 1, 2, 4, 8, 10, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 64, 68, 72, 76, 80 };     // For Castor
    const int numRuns = 10;                                           // Number of runs
    // const int numRuns = 1;                                           // Number of runs
    const long numPairs = 1*MILLION;                                 // 1M is fast enough on the laptop
    const int numSameOps = 100;

    std::tuple<uint64_t, double, double, double, double, double> results[threadList.size()];
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
    pdataFile << "DFC-PWB" << "\t" << "DFC-PFENCE" << "\t" << "DFC-PWB-T" << "\t" << "DFC-PFENCE-T" << "\t" << "DFC-COMBINING" << "\t";
    pdataFile << "\n";
    for (int it = 0; it < threadList.size(); it++) {
        pdataFile << threadList[it] << "\t";
        pdataFile << std::get<1>(results[it]) << "\t";
        pdataFile << std::get<2>(results[it]) << "\t";
        pdataFile << std::get<3>(results[it]) << "\t";
        pdataFile << std::get<4>(results[it]) << "\t";
        pdataFile << std::get<5>(results[it]) << "\t";
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

    pool<examples::pmem_queue> pop;
    persistent_ptr<examples::pmem_queue> q;

    try {
        if (file_exists(path) != 0) {
            pop = pool<examples::pmem_queue>::create(
                    path, LAYOUT, PMEMOBJ_MIN_POOL, (S_IWUSR | S_IRUSR));
        } else {
            pop = pool<examples::pmem_queue>::open(path, LAYOUT);
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
                q->push(pop, std::stoull(argv[3]));
            } catch (const std::runtime_error &e) {
                std::cerr << "Exception: " << e.what()
                          << std::endl;
                return 1;
            }
            break;
        case QUEUE_POP:
            try {
                std::cout << q->pop(pop) << std::endl;
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
            q->show();
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