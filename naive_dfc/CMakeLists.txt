cmake_minimum_required(VERSION 3.3)
project(naive_dfc CXX)


set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

#set (CMAKE_CXX_FLAGS "-O2 -DCOUNT_PWB -DRANDOP")
#set (CMAKE_CXX_FLAGS "-O2 -DPWB_IS_CLFLUSHOPT -DRANDOP")
#set (CMAKE_CXX_FLAGS "-O2 -DPWB_IS_CLFLUSHOPT -DSAME100_BENCH")
#set (CMAKE_CXX_FLAGS "-O2 -DCOUNT_PWB -DSAME100_BENCH")
#set (CMAKE_CXX_FLAGS "-O2 -DPWB_IS_CLFLUSHOPT")
#set (CMAKE_CXX_FLAGS "-O2 -DPWB_IS_PMEM")
#set (CMAKE_CXX_FLAGS "-O2 -DPWB_IS_CLFLUSH")
set (CMAKE_CXX_FLAGS "-O2 -DCOUNT_PWB")

include(FindThreads)

if(NOT WIN32)
	find_package(PkgConfig QUIET)
endif()

if(PKG_CONFIG_FOUND)
	pkg_check_modules(LIBPMEMOBJ++ REQUIRED libpmemobj++)
else()
	find_package(LIBPMEMOBJ++ REQUIRED)
endif()

link_directories(${LIBPMEMOBJ++_LIBRARY_DIRS})

add_executable(naive_dfc dfc.cpp)
target_include_directories(naive_dfc PUBLIC ${LIBPMEMOBJ++_INCLUDE_DIRS} . ..)
target_link_libraries(naive_dfc ${LIBPMEMOBJ++_LIBRARIES} ${CMAKE_THREAD_LIBS_INIT} pmem)
