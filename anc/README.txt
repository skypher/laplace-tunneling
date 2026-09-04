The files in this directory reproduce the fixed-mesh numerical checks in
Tables 1 and 2 of the manuscript.

Files
-----
check_asymptotics.py        Exact cell-integral Galerkin calculation
requirements-numerics.txt   Pinned NumPy and SciPy versions
asymptotics_180.txt         Reference output for the 180-cell calculation

Reproduction
------------
From this directory, run:

    python3 -u -m pip install -r requirements-numerics.txt
    python3 -u check_asymptotics.py

Before solving the eigenproblems, the script checks the assembled
constant-function energy identity and the exact reuse of each translated
one-well block.  It prints progress after each separation and supports both
-h and --help.

The reference output was reproduced using Python 3.12.3, NumPy 1.26.4, and
SciPy 1.11.4.  The manuscript rounds the one-well quantities and scaled shifts
to six decimal places; asymptotics_180.txt retains the more precise output.  The
maximum scaled-shift errors are computed before rounding.
