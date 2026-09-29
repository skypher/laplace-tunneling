#!/bin/bash
# usage: final_check.sh  -- full lake build, sorry census, statement check, axiom audit
if [ "$1" = "-h" ] || [ "$1" = "--help" ]; then echo "usage: final_check.sh (full build + sorry census + stmtcheck + axioms)"; exit 0; fi
cd /home/yang/tunnel/lean
export PATH="$HOME/.elan/bin:$PATH"
stdbuf -oL lake build > logs/skeleton/final_build.log 2>&1; echo "build exit=$? $(tail -1 logs/skeleton/final_build.log)"
echo "sorry warnings by file:"; grep "declaration uses .sorry." logs/skeleton/final_build.log | sed -E 's/.*(Tunneling\/[^:]*).*/\1/' | sort | uniq -c
echo "sorry tokens in sources:"; grep -cE "\bsorry\b" Tunneling/*.lean Tunneling/*/*.lean | grep -v ":0$"
echo "axiom decls:"; grep -nE "^\s*axiom\b" Tunneling/*.lean Tunneling/*/*.lean
python3 logs/skeleton/stmtcheck.py | tail -3
lake env lean logs/skeleton/Axioms.lean 2>&1 | tee logs/skeleton/axioms_final.log
