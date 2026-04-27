cmake_minimum_required(VERSION 3.16)
project(soplex_prover LANGUAGES CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# ---- User-tunable settings ----
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Set this to your local dependency prefix, e.g. $HOME/local
# You can pass it at configure time:
#   cmake -S . -B build -DLOCAL_PREFIX=$HOME/local
set(LOCAL_PREFIX "$ENV{LOCAL_PREFIX}" CACHE PATH "Prefix containing local third-party libs and headers")

# Reasonably portable release flags; you can edit these if needed.
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

# ---- Source ----
add_executable(soplex-prover soplex-prover.cpp)

# ---- Optional local include/lib search paths ----
if(LOCAL_PREFIX)
  target_include_directories(soplex-prover PRIVATE "${LOCAL_PREFIX}/include")
  link_directories("${LOCAL_PREFIX}/lib" "${LOCAL_PREFIX}/lib64")
endif()

# ---- Find libraries ----
# These names assume the usual shared library filenames:
#   libtbb.so, libtbbmalloc.so, libsoplex.so, libmpfr.so, libgmp.so, libz.so
# If your distro uses different names/paths, adjust LOCAL_PREFIX or the library names below.

find_library(TBB_LIB       NAMES tbb       PATHS "${LOCAL_PREFIX}/lib" "${LOCAL_PREFIX}/lib64" NO_DEFAULT_PATH)
find_library(TBBMALLOC_LIB NAMES tbbmalloc PATHS "${LOCAL_PREFIX}/lib" "${LOCAL_PREFIX}/lib64" NO_DEFAULT_PATH)
find_library(SOPEX_LIB     NAMES soplex    PATHS "${LOCAL_PREFIX}/lib" "${LOCAL_PREFIX}/lib64" NO_DEFAULT_PATH)
find_library(MPFR_LIB      NAMES mpfr      PATHS "${LOCAL_PREFIX}/lib" "${LOCAL_PREFIX}/lib64" NO_DEFAULT_PATH)
find_library(GMP_LIB       NAMES gmp       PATHS "${LOCAL_PREFIX}/lib" "${LOCAL_PREFIX}/lib64" NO_DEFAULT_PATH)
find_library(ZLIB_LIB      NAMES z         PATHS "${LOCAL_PREFIX}/lib" "${LOCAL_PREFIX}/lib64" NO_DEFAULT_PATH)

# Fallback to system paths if not found in LOCAL_PREFIX.
if(NOT TBB_LIB)
  find_library(TBB_LIB NAMES tbb)
endif()
if(NOT TBBMALLOC_LIB)
  find_library(TBBMALLOC_LIB NAMES tbbmalloc)
endif()
if(NOT SOPEX_LIB)
  find_library(SOPEX_LIB NAMES soplex)
endif()
if(NOT MPFR_LIB)
  find_library(MPFR_LIB NAMES mpfr)
endif()
if(NOT GMP_LIB)
  find_library(GMP_LIB NAMES gmp)
endif()
if(NOT ZLIB_LIB)
  find_library(ZLIB_LIB NAMES z)
endif()

# Hard fail early with a clear message.
foreach(_lib IN ITEMS TBB_LIB TBBMALLOC_LIB SOPEX_LIB MPFR_LIB GMP_LIB ZLIB_LIB)
  if(NOT ${_lib})
    message(FATAL_ERROR "Missing dependency: ${_lib}. Set LOCAL_PREFIX to the directory that contains the library, or install the shared library locally.")
  endif()
endforeach()

# ---- Link ----
target_link_libraries(soplex-prover PRIVATE
  ${TBB_LIB}
  ${TBBMALLOC_LIB}
  ${SOPEX_LIB}
  ${MPFR_LIB}
  ${GMP_LIB}
  ${ZLIB_LIB}
  pthread
)

# ---- Portable runtime lookup ----
# Let the binary look for its .so files next to itself.
set_target_properties(soplex-prover PROPERTIES
  BUILD_RPATH "$ORIGIN"
  INSTALL_RPATH "$ORIGIN"
)

# ---- Optional: copy the directly linked shared libraries next to the executable ----
# This makes it easier to upload a single folder to the server.
set(_bundle_dir "$<TARGET_FILE_DIR:soplex-prover>")
foreach(_lib IN ITEMS
  ${TBB_LIB}
  ${TBBMALLOC_LIB}
  ${SOPEX_LIB}
  ${MPFR_LIB}
  ${GMP_LIB}
  ${ZLIB_LIB}
)
  if(EXISTS "${_lib}")
    add_custom_command(TARGET soplex-prover POST_BUILD
      COMMAND ${CMAKE_COMMAND} -E copy_if_different "${_lib}" "${_bundle_dir}"
      VERBATIM
    )
  endif()
endforeach()

message(STATUS "Using TBB       : ${TBB_LIB}")
message(STATUS "Using TBBMALLOC : ${TBBMALLOC_LIB}")
message(STATUS "Using SoPlex    : ${SOPEX_LIB}")
message(STATUS "Using MPFR      : ${MPFR_LIB}")
message(STATUS "Using GMP       : ${GMP_LIB}")
message(STATUS "Using Zlib      : ${ZLIB_LIB}")

