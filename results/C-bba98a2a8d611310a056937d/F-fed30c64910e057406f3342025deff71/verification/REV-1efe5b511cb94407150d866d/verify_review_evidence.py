"""Read-only verification of request-bound materials and execution evidence."""
from pathlib import Path
import sys,json,re,hashlib
R=Path('E:/数学总目录');sys.path.insert(0,str(R/'astra-math-workflow-v2'))
from mathflow.core import read_json,file_hash,inventory,digest
job=R/'review-jobs/QP01-public-formal-audit-20261105';out=Path(__file__).parent
req=read_json(job/'request.json');records=[]
for item in req['materials']:
 p=job/'materials'/item['path'];assert p.is_file() and p.stat().st_size==item['size'] and file_hash(p)==item['sha256'],item['path']
for item in req['execution_records']:
 folder=job/'execution-checks'/item['check_id'];observed=digest(inventory(folder));assert observed==item['record_sha256'],(item['check_id'],observed)
 result=read_json(folder/'result.json')
 assert result['package_manifest_sha256']==req['manifest_sha256'] and result['package_id']==req['package_id'] and result['claim_id']==req['claim_id'] and result['passed']==item['passed']
 for i,cmd in enumerate(result['commands'],1):
  assert file_hash(folder/f'step-{i}.log')==cmd['log_sha256']
  receipt=read_json(folder/f'step-{i}.log.result.json');assert receipt['returncode']==cmd['returncode'] and receipt['timed_out']==cmd['timed_out']
 records.append({'check_id':item['check_id'],'record_sha256':observed,'passed':result['passed'],'error':result.get('error')})
latest=job/'execution-checks'/req['execution_records'][-1]['check_id'];res=read_json(latest/'result.json')
assert res['passed'] and res['checker_passed'] and len(res['commands'])==3
assert all(c['returncode']==0 and not c['timed_out'] for c in res['commands'])
build=(latest/'step-1.log').read_text(encoding='utf-8');modules=sorted(p.stem for p in (job/'materials/lean').glob('*.lean'))
built=set(re.findall(r'\bBuilt ([A-Za-z][A-Za-z0-9_]*) \(',build));assert set(modules)<=built,sorted(set(modules)-built)
assert 'Build completed successfully (2478 jobs).' in build and 'sorryAx' not in build
allowed={'propext','Classical.choice','Quot.sound'};groups=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',build)
assert all({x.strip() for x in group.split(',') if x.strip()}<=allowed for group in groups)
targets=['PartitionLaguerre.main_classification_proved','PartitionLaguerre.above_threshold_failure_proved']
for target in targets:assert f"'{target}' depends on axioms: [propext, Classical.choice, Quot.sound]" in build
assert '--fresh' in res['commands'][2]['argv'] and res['commands'][2]['argv'][-1]=='AuditFinalQP01'
dep=read_json(latest/'dependency-source-verification.json');stability=read_json(latest/'dependency-object-stability.json')
assert stability['unchanged'] and stability['object_count']==len(dep['object_sha256'])==27147
lock=read_json(job/'materials/lean/lake-manifest.json');assert {p['name']:p['rev'] for p in lock['packages']}=={p['name']:p['revision'] for p in dep['dependencies']}
mapping=read_json(latest/'dependency-overrides.json');assert {p['name'] for p in mapping['packages']}=={p['name'] for p in lock['packages']}
dirs={p['name']:Path(p['dir']) for p in mapping['packages']}
for package in dep['dependencies']:
 for item in package['source_files_verified']:
  p=dirs[package['name']]/item['path'];b=p.read_bytes()
  assert hashlib.sha256(b).hexdigest()==item['sha256'],str(p)
  assert hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==item['git_blob'],str(p)
assert file_hash(latest/'collector-dependency-adapter.py')==file_hash(R/'ops/check_qp01_cached.py')
summary={'request_id':req['request_id'],'material_files_verified':len(req['materials']),'execution_records':records,'project_modules_built':modules,'project_module_count':len(modules),'axiom_report_occurrences_checked':len(groups),'full_targets_checked':targets,'dependency_source_count':sum(len(p['source_files_verified']) for p in dep['dependencies']),'dependency_source_bytes_independently_rehashed':True,'dependency_objects_stable':stability['object_count'],'warning_count':len(re.findall(r'^warning:',build,re.M)),'result':'all request/hash/coverage assertions passed'}
(out/'evidence-verification.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in summary.items() if k not in ('project_modules_built','execution_records')},ensure_ascii=False))
