from pathlib import Path
import datetime as dt,hashlib,json,subprocess,time
R=Path(__file__).resolve().parent;P=R.parent/'proof196/problems/erdos-196/lean/reproduction';env=json.loads((R/'environment.json').read_text());bin33=Path(env['PATH'].split(':')[0]);nanoda=Path('/Users/jenwin/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/nanoda_bin')
profile=R/'sandbox.sb';profile.write_text(profile.read_text()+f'(allow file-read* (literal {json.dumps(str(nanoda))}))\n')
for i in range(300):
 result=json.loads((R/'result.json').read_text())
 if result['status']!='RUNNING':break
 time.sleep(1)
assert result['status']=='SOURCE_BUILD_AUDIT_AND_KERNEL_REPLAY_PASSED',result['status']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def command(label,args,export=False):
 log=R/'logs'/f'{label}.log';t=time.monotonic();argv=['/usr/bin/sandbox-exec','-f',str(profile),*map(str,args)];print('START',label,flush=True)
 with (R/'Erdos196.ndjson' if export else log).open('wb') as out:
  with (R/'logs/export-stderr.log').open('wb') if export else open('/dev/null','wb') as err:
   p=subprocess.run(argv,cwd=P,env=env,stdout=out,stderr=err if export else subprocess.STDOUT)
 row={'label':label,'argv':argv,'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3),'output':'Erdos196.ndjson' if export else str(log.relative_to(R))};result['commands'].append(row);print('FINISH',label,p.returncode,row['seconds'],flush=True)
 (R/'result.json').write_text(json.dumps(result,indent=2)+'\n');assert p.returncode==0,label
command('detailed-targets',[bin33/'lake','env','lean','--trust=0',R/'Detailed196.lean'])
command('bridge-object',[bin33/'lake','env','lean','--trust=0','-o',P/'.lake/build/lib/lean/Independent196.olean',R/'Independent196.lean'])
command('export-targets',[bin33/'lake','env',R/'exporter/.lake/build/bin/lean4export','Independent196','--','Bounty.target','Bounty.paper_main','checked196'],True)
config={'export_file_path':str(R/'Erdos196.ndjson'),'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'unsafe_permit_all_axioms':False,'nat_extension':True,'string_extension':True,'pp_declars':['Intended196','Bounty.target','Bounty.paper_main','checked196'],'pp_to_stdout':True,'print_success_message':True,'pp_options':{'proofs':False,'width':120}}
(R/'nanoda.json').write_text(json.dumps(config,indent=2)+'\n')
command('nanoda',[nanoda,R/'nanoda.json'])
result.update(status='SOURCE_BUILD_AXIOMS_KERNEL_AND_NANODA_PASSED',export_sha256=sha(R/'Erdos196.ndjson'),export_bytes=(R/'Erdos196.ndjson').stat().st_size,completed_utc=dt.datetime.now(dt.timezone.utc).isoformat());(R/'result.json').write_text(json.dumps(result,indent=2)+'\n')
