cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

project(maplesat)

#--------------------------------------------------------------------------------------------------
# Configurable options:

option(STATIC_BINARIES "Link binaries statically." ON)
option(USE_SORELEASE   "Use SORELEASE in shared library filename." ON)

#--------------------------------------------------------------------------------------------------
# Library version:

set(MAPLESAT_SOMAJOR   2)
set(MAPLESAT_SOMINOR   1)
set(MAPLESAT_SORELEASE 0)

# Compute VERSION and SOVERSION:
if (USE_SORELEASE)
  set(MAPLESAT_VERSION ${MAPLESAT_SOMAJOR}.${MAPLESAT_SOMINOR}.${MAPLESAT_SORELEASE})
else()
  set(MAPLESAT_VERSION ${MAPLESAT_SOMAJOR}.${MAPLESAT_SOMINOR})
endif()
set(MAPLESAT_SOVERSION ${MAPLESAT_SOMAJOR})

#--------------------------------------------------------------------------------------------------
# Dependencies:

find_package(ZLIB)
include_directories(${ZLIB_INCLUDE_DIR})
include_directories(${maplesat_SOURCE_DIR})

#--------------------------------------------------------------------------------------------------
# Compile flags:

add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)

#--------------------------------------------------------------------------------------------------
# Build Targets:

set(MAPLESAT_LIB_SOURCES
    maplesat/utils/Options.cc
    maplesat/utils/System.cc
    maplesat/core/Solver.cc
    maplesat/simp/SimpSolver.cc)

add_library(maplesat-lib-static STATIC ${MAPLESAT_LIB_SOURCES})
add_library(maplesat-lib-shared SHARED ${MAPLESAT_LIB_SOURCES})

target_link_libraries(maplesat-lib-shared ${ZLIB_LIBRARY})
target_link_libraries(maplesat-lib-static ${ZLIB_LIBRARY})

add_executable(maplesat_core maplesat/core/Main.cc)
add_executable(maplesat_simp maplesat/simp/Main.cc)

if(STATIC_BINARIES)
  target_link_libraries(maplesat_core maplesat-lib-static)
  target_link_libraries(maplesat_simp maplesat-lib-static)
else()
  target_link_libraries(maplesat_core maplesat-lib-shared)
  target_link_libraries(maplesat_simp maplesat-lib-shared)
endif()

set_target_properties(maplesat-lib-static PROPERTIES  OUTPUT_NAME "maplesat")
set_target_properties(maplesat-lib-shared
  PROPERTIES
    OUTPUT_NAME "maplesat" 
    VERSION ${MAPLESAT_VERSION}
    SOVERSION ${MAPLESAT_SOVERSION})

set_target_properties(maplesat_simp       PROPERTIES OUTPUT_NAME "maplesat_simp")

#--------------------------------------------------------------------------------------------------
# Installation targets:

install(TARGETS maplesat-lib-static maplesat-lib-shared maplesat_core maplesat_simp 
        RUNTIME DESTINATION bin
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib)

install(DIRECTORY maplesat/mtl maplesat/utils maplesat/core maplesat/simp
        DESTINATION include/maplesat
        FILES_MATCHING PATTERN "*.h")
