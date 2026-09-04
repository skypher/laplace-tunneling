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

The second command checks the exact assembly identities before computing the
one-, two-, and three-well eigenvalue data.  It supports both -h and --help.
