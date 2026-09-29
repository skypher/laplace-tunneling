#!/usr/bin/env python3
"""Extract the last type-checked full file from an agent's JSON log.
usage: extract_checked.py [-h] NAME TARGETPATH [OUT]
Scans NAME.jsonl / NAME.r*.jsonl for completed `lean --stdin` commands whose heredoc
contains every theorem name of the frozen TARGETPATH, reports each candidate
(exit code, error lines, sorry count) and writes the newest error-free one to OUT."""
import sys, json, re, glob, os
if len(sys.argv)<3 or sys.argv[1] in ('-h','--help'): print(__doc__); sys.exit(0)
name,target=sys.argv[1],sys.argv[2]
out=sys.argv[3] if len(sys.argv)>3 else f'/tmp/claude_checked_{name}.lean'
root='/home/yang/tunnel/lean'
frozen=open(root+'/logs/skeleton/frozen/'+target.replace('Tunneling/','')).read()
names=re.findall(r'^(?:noncomputable )?theorem (\S+)',frozen,re.M)
logs=sorted(glob.glob(f'{root}/logs/agents/{name}.jsonl')+glob.glob(f'{root}/logs/agents/{name}.r*.jsonl'),key=os.path.getmtime)
cands=[]
for lg in logs:
    for line in open(lg):
        try: e=json.loads(line)
        except: continue
        it=e.get('item',{})
        if e.get('type')!='item.completed' or it.get('type')!='command_execution': continue
        cmd=it.get('command','')
        if '--stdin' not in cmd: continue
        try:
            import shlex
            parts=shlex.split(cmd)
            if len(parts)>=3 and parts[1] in ('-lc','-c'): cmd=parts[2]
        except Exception: pass
        m=re.search(r"<<'?(\w+)'?\n(.*?)\n\1\b",cmd,re.S)
        if not m: continue
        body=m.group(2)
        if '\\`' in body or '\\$' in body:
            body=body.replace('\\`','`').replace('\\$','$')
        if not all(re.search(r'theorem '+re.escape(n)+r'\b',body) for n in names): continue
        o=it.get('aggregated_output') or ''
        errs=len(re.findall(r'error',o)); sor=len(re.findall(r'\bsorry\b',body))
        cands.append((lg,it.get('exit_code'),errs,sor,body,o))
for i,(lg,ex,er,so,b,o) in enumerate(cands):
    print(i,os.path.basename(lg),'exit',ex,'errlines',er,'sorry-tokens',so,'lines',b.count('\n')+1)
good=[c for c in cands if c[2]==0 and c[1] in (0,1)]
if good:
    b=good[-1][4]
    open(out,'w').write(b+'\n'); print('wrote',out,'from candidate with sorry-tokens',good[-1][3])
else: print('no error-free full candidate')
