[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)

# Yices-NTA

This repository contains the first iteration of the tool Yices-NTA, 
a tool for solving Non-Linear Transcendental Arithmetic (NTA).
The tool is based on the 
[Satisfiability Modulo Theories](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) (SMT) solver 
[Yices2](https://github.com/SRI-CSL/yices2). 

The repository at [github.com/nta-labs/experimental-evaluation-feb26](https://github.com/nta-labs/experimental-evaluation-feb26)
Contains an experimental evaluation of the tool.

# Installation (Unix systems)

On top of the libraries required by Yices2 in order to run in MCSAT mode, 
we require the library FLINT to perform interval arithmetic in arbitrary precision.
Here is a short guide for the installation:

1. Install SRI's library for polynomial manipulation. It's available
   on [github](https://github.com/SRI-CSL/libpoly).

2. Install the CUDD library for binary-decision diagrams. We recommend
   using the github distribution: https://github.com/ivmai/cudd.

3. Install the FLINT libary: https://flintlib.org/. 

4. After you've installed libpoly, CUDD and FLINT, perform the following:

```
autoconf
./configure --enable-mcsat
make
```
The binary will be placed in `./build/x86_64-pc-linux-gnu-release/bin/yices_smt2

## Troubleshooting

1. You may need to provide `LDFLAGS/CPPFLAGS` if `./configure` fails to
  find the libpoly, CUDD or FLINT libraries. Other options may be useful too.  
  Try `./configure --help` to see what's there.

2. We only use the ARB module of FLINT. This used to be a separated library. 
   Depending on the version of FLINT, or on whether you already had ARB installed 
   in your system, it might happen that arb.h and arf.h ends up in /usr/include/ 
   instead of /usr/include/flint. If that's the case, a possible fix is to modify the 
   source code of the tool, updating the includes
   `#include <flint/arb.h>` and `#include <flint/arf.h>` 
   to `#include <arb.h>` and `#include <arf.h>`. These appear only in the files 
   `src/mcsat/na/nta_functions.h` and `src/mcsat/na/nta_functions.c`.

## Diff with Yices2 

Apart form the commit adding this README, the repository contains 
[another commit](https://github.com/nta-labs/yices-nta/commit/5a55cdb8408ba82958e39a5c08313df697d59fff)
that applies all updates needed to extend Yices2 to Yices-NTA. You can 
inspect the differences between the two tools by inspecting that commit.