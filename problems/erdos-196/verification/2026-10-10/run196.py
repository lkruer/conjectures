from pathlib import Path
import datetime as dt,hashlib,json,os,subprocess,time
RUN=Path(__file__).resolve().parent;P=RUN.parent/'proof196/problems/erdos-196/lean/reproduction';TC=Path('/Users/jenwin/.elan/toolchains/leanprover--lean4---v4.33.1');env=json.loads((RUN/'environment.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
result={'status':'RUNNING','started_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'proof_commit':'bf058b903350eb8f873a22ab4a54b2e0faa9727d','commands':[],'initial_source_hashes':{x:sha(P/x) for x in ['Erdos196.lean','PaperMain.lean','Audit.lean','TaskSupport.lean','lake-manifest.json']}}
def save(): (RUN/'result.json').write_text(json.dumps(result,indent=2)+'\n')
def command(label,argv):
 start=time.monotonic();log=RUN/'logs'/f'{label}.log';args=['/usr/bin/sandbox-exec','-f',str(RUN/'sandbox.sb'),*map(str,argv)];print('START',label,flush=True)
 with log.open('wb') as s:p=subprocess.run(args,cwd=P,env=env,stdout=s,stderr=subprocess.STDOUT)
 row={'label':label,'argv':args,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3),'log':str(log.relative_to(RUN)),'sha256':sha(log)};result['commands'].append(row);save();print('FINISH',label,p.returncode,row['seconds'],flush=True);assert p.returncode==0,log
 return log.read_text(errors='replace')
try:
 command('version',[TC/'bin/lake','env','lean','--version'])
 command('utilities',[TC/'bin/lake','build','FormalConjecturesUtil','TaskSupport'])
 statement=P/'.dependencies/formal-conjectures/.lake/build/lib/lean/FormalConjectures/ErdosProblems/196.olean';statement.parent.mkdir(parents=True,exist_ok=True)
 command('statement',[TC/'bin/lake','env','lean','--trust=0','--root=.dependencies/formal-conjectures','-Dgoogle.answer=always_true','-o',statement,'.dependencies/formal-conjectures/FormalConjectures/ErdosProblems/196.lean'])
 (P/'.lake/build/lib/lean').mkdir(parents=True,exist_ok=True)
 for x in ['Erdos196','PaperMain']:command(x,[TC/'bin/lake','env','lean','--trust=0','-o',P/f'.lake/build/lib/lean/{x}.olean',x+'.lean'])
 command('audit',[TC/'bin/lake','env','lean','--trust=0','Audit.lean'])
 bridge=RUN/'Independent196.lean';bridge.write_text('''import PaperMain

def Intended196 : Prop := ∃ p : ℕ ≃ ℕ, ∀ a b c d : ℕ,
  a < b → b < c → c < d →
  ¬ (p a + p c = 2 * p b ∧ p b + p d = 2 * p c)
theorem checked196 : Intended196 := Bounty.paper_main
#check @checked196
#print checked196
#print axioms checked196
#print HasMonotoneAP
''')
 command('independent-bridge',[TC/'bin/lake','env','lean','--trust=0',bridge])
 command('kernel-replay',[TC/'bin/lake','env','leanchecker','--verbose','Erdos196','PaperMain'])
 result['source_unchanged']=all(sha(P/x)==h for x,h in result['initial_source_hashes'].items());assert result['source_unchanged'];result['status']='SOURCE_BUILD_AUDIT_AND_KERNEL_REPLAY_PASSED';result['completed_utc']=dt.datetime.now(dt.timezone.utc).isoformat()
except BaseException as e:result.update(status='FAILED',error=str(e));raise
finally:save()
