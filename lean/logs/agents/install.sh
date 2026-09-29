#!/bin/bash
# usage: install.sh SRCFILE TARGET(relative to lean/)  -- back up target, install src, compile, scan, stmtcheck
if [ "$1" = "-h" ] || [ "$1" = "--help" ] || [ -z "$2" ]; then echo "usage: install.sh SRC TARGET  (backup, install, lake env lean, forbidden scan, stmtcheck)"; exit 0; fi
cd /home/yang/tunnel/lean
mkdir -p logs/agents/backup
cp "$2" "logs/agents/backup/$(basename $2).$(date +%H%M%S)"
cp "$1" "$2"
b=$(basename $2 .lean)
PATH="$HOME/.elan/bin:$PATH" lake env lean "$2" > logs/agents/check_$b.log 2>&1; echo "compile exit=$?"
grep -nE "error|declaration uses .sorry." logs/agents/check_$b.log | head -20
echo "forbidden:"; grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|\bunsafe\b|implemented_by|set_option debug|@\[csimp" "$2"
python3 logs/skeleton/stmtcheck.py "${2#Tunneling/}" | tail -3
