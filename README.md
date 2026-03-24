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

1. Install GNU [gperf](https://www.gnu.org/software/gperf/).

1. Install SRI's library for polynomial manipulation. It's available
   on [github](https://github.com/SRI-CSL/libpoly).

2. Install the CUDD library for binary-decision diagrams. We recommend
   using the github distribution: https://github.com/ivmai/cudd. During installation, 
   run `./configure` with option `--enable-shared`.

3. Install the FLINT libary: https://flintlib.org/. 

4. After you've installed libpoly, CUDD and FLINT, perform the following:

```
autoconf
./configure --enable-mcsat
make
```
The binary will be placed in `./build/x86_64-pc-linux-gnu-release/bin/yices_smt2

## Troubleshooting

1. During Step 2 (CUDD installation), `make` might throw an error 
   `[Makefile:983: aclocal.m4] Error 127`. In this case, perform `autoreconf -fi` 
   and run again `./configure --enable-shared`.

2. We only use the ARB module of FLINT. This used to be a separated library. 
   Depending on the version of FLINT, or on whether you already had ARB installed 
   in your system, it might happen that `arb.h` and `arf.h` ends up in `/path/to/include/`
   instead of `/path/to/include/flint`. If that's the case, a possible fix is 
   to modify the source code of the tool, updating the includes
   `#include <flint/arb.h>` and `#include <flint/arf.h>` 
   to `#include <arb.h>` and `#include <arf.h>`. These appear only in the files 
   `src/mcsat/tra/tra_functions.h` and `src/mcsat/tra/tra_functions.c`.

1. As usual, you may need to provide `LDFLAGS/CPPFLAGS` if `./configure` fails to
   find the relevant libraries. Other options may be useful too.  
   Try `./configure --help` to see what's there.

# Running the tool 

Given an instance.smt2 file, run the tool with: 

`./build/x86_64-pc-linux-gnu-release/bin/yices_smt2 instance.smt2`

The input file should contain `(set-logic QF_NRA)` at the beginning of the file. 
Functions `sin` and `exp`, as well as the constant `pi` must be defined explicitly in the file, 
even thought they are treated as interpreted functions. Here is an example:

```
(set-logic QF_NRA)
(declare-fun sin (Real) Real)
(declare-fun pi () Real)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_0 () Real)
(assert (let ((.def_10 (* (/ 1 2) pi)))
(let ((.def_25 (+ .def_10 x_1)))
(let ((.def_26 (sin .def_25)))
(let ((.def_27 (/ x_1 .def_26)))
(let ((.def_28 (= x_2 .def_27)))
(let ((.def_17 (= x_0 x_1)))
(let ((.def_15 (= x_0 (+ 0 2))))
(let ((.def_18 (and .def_15 .def_17)))
(let ((.def_29 (and .def_18 .def_28)))
(let ((.def_23 (= x_1 (+ 0 2))))
(let ((.def_30 (and .def_23 .def_29)))
.def_30))))))))))))
(check-sat)
```
If you want to print the model, add the options `--yices-model-format --dump-models`. 
Note that, in addition to variables, these options may show assignments to arbitrary terms. 
When verifying a solution, ignore values assigned to these terms, as they are artifacts of 
internal computations performed by the tool.

# Diff with Yices2 

The commit [5a55cdb8](https://github.com/nta-labs/yices-nta/commit/5a55cdb8408ba82958e39a5c08313df697d59fff)
applies all updates needed to extend Yices2 to Yices-NTA. You can 
inspect the differences between the two tools by inspecting that commit.