#!/usr/bin/env python3
"""Compare theorem/def signatures of skeleton files against the frozen copy.
usage: stmtcheck.py [-h] [FILE...]   (paths relative to lean/, default: all frozen files)
Prints CHANGED/MISSING for any locked declaration whose signature text differs."""
import sys, re, os, glob
if any(a in ('-h','--help') for a in sys.argv[1:]):
    print(__doc__); sys.exit(0)
root='/home/yang/tunnel/lean'
frozen=os.path.join(root,'logs/skeleton/frozen')
def sigs(text):
    out={}
    # declaration header up to ':= by' or ':=' or ' where'
    for m in re.finditer(r'^(?:noncomputable )?(theorem|def|structure|abbrev) (\S+)(.*?)(?=:= by|:=\s|\swhere\b)', text, re.S|re.M):
        name=m.group(2); body=' '.join(m.group(3).split())
        out[name]=body
    return out
files=sys.argv[1:] or [os.path.relpath(p,frozen) for p in glob.glob(frozen+'/**/*.lean',recursive=True)]
bad=0
for f in files:
    rel=f.replace('Tunneling/','')
    fz=os.path.join(frozen,rel); cur=os.path.join(root,'Tunneling',rel)
    a=sigs(open(fz).read()); b=sigs(open(cur).read())
    for k,v in a.items():
        if k not in b: print('MISSING',rel,k); bad+=1
        elif b[k]!=v: print('CHANGED',rel,k); bad+=1
print('stmtcheck: %d problems'%bad)
