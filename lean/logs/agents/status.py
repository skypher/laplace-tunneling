#!/usr/bin/env python3
"""Per-agent progress: lean runs, last lean error count, commands, tokens, finished?
usage: status.py [-h]"""
import sys, json, os, glob, time, re
if any(a in ('-h','--help') for a in sys.argv[1:]): print(__doc__); sys.exit(0)
d='/home/yang/tunnel/lean/logs/agents'
starts={}
for l in open(d+'/dispatch.log'):
    m=re.match(r'(\S+ \S+) launch (\S+)',l)
    if m: starts[m.group(2)]=m.group(1)
now=time.time()
print(time.strftime('%F %T'),'agents:',len(starts))
done=0
for name in sorted(starts):
    cands=sorted(glob.glob(f'{d}/{name}.jsonl')+glob.glob(f'{d}/{name}.r*.jsonl'),key=os.path.getmtime)
    if not cands: print(name,'no log'); continue
    p=cands[-1]; rnd=os.path.basename(p).split('.')[1] if p.count('.')>1 else 'r1'
    cmds=lean=0; lasterr=None; fin=False; failed=None; tok=0
    for l in open(p):
        try: e=json.loads(l)
        except: continue
        t=e.get('type')
        if t=='turn.completed':
            fin=True; tok=e.get('usage',{}).get('output_tokens',tok)
        if t in ('turn.failed','error'): failed=str(e)[:120]
        it=e.get('item',{})
        if t=='item.completed' and it.get('type')=='command_execution':
            cmds+=1
            if '--stdin' in it.get('command',''):
                lean+=1; out=it.get('aggregated_output') or ''
                lasterr=len(re.findall(r'error',out))
    age=int(now-os.path.getmtime(p))
    last=os.path.exists(f'{d}/{name}.last.md') and os.path.getsize(f'{d}/{name}.last.md')>0
    done+=fin or bool(failed)
    t0=time.mktime(time.strptime(starts[name],'%Y-%m-%d %H:%M:%S'))
    print(f'{name:9s} {rnd:3s} run={int((now-t0)/60):4d}m cmds={cmds:4d} leanruns={lean:3d} lastLeanErrLines={lasterr} idle={age:4d}s finished={fin} deliverable={last} {"FAILED "+failed if failed else ""}')
print('finished',done,'/',len(starts))
