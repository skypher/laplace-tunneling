#!/usr/bin/env python3
"""Install an agent's delivered file and check it.
usage: integrate.py [-h] NAME [--dry]
Extracts the file between ===BEGIN FILE <path>=== / ===END FILE=== from NAME.last.md,
backs up the current file to logs/agents/backup/, writes it (unless --dry: writes to /tmp only),
runs forbidden-token scan and stmtcheck. Compilation is done separately with lake."""
import sys, re, os, shutil, time, subprocess
if len(sys.argv)<2 or sys.argv[1] in ('-h','--help'): print(__doc__); sys.exit(0)
name=sys.argv[1]; dry='--dry' in sys.argv
root='/home/yang/tunnel/lean'; d=root+'/logs/agents'
txt=open(f'{d}/{name}.last.md').read()
m=re.search(r'===BEGIN FILE (\S+)===\n(.*?)(?:\n?===END FILE[^\n]*|\Z)',txt,re.S)
if not m: print('NO FILE BLOCK'); sys.exit(2)
path,content=m.group(1),m.group(2)
if content.startswith('```'):
    content=re.sub(r'^```\w*\n','',content); content=re.sub(r'\n```\s*$','',content)
bad=[t for t in [r'\bsorry\b',r'\badmit\b',r'native_decide',r'^\s*axiom\b',r'\bunsafe\b',r'implemented_by',r'@\[extern',r'set_option debug',r'@\[csimp'] if re.search(t,content,re.M)]
print('file',path,'lines',content.count('\n')+1,'forbidden:',bad)
target=os.path.join(root,path)
if dry:
    open('/tmp/claude_integrate_'+name+'.lean','w').write(content+'\n'); print('dry: wrote /tmp/claude_integrate_'+name+'.lean'); sys.exit(0)
os.makedirs(d+'/backup',exist_ok=True)
shutil.copy(target,f'{d}/backup/{os.path.basename(path)}.{time.strftime("%H%M%S")}')
open(target,'w').write(content if content.endswith('\n') else content+'\n')
print(subprocess.run(['python3',root+'/logs/skeleton/stmtcheck.py',path.replace('Tunneling/','')],capture_output=True,text=True).stdout)
