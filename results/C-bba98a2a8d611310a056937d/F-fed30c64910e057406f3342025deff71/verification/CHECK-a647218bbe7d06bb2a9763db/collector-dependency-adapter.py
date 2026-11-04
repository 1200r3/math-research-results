"""Original collector with explicit Lake --packages dependency-cache arguments.

Only third-party dependency outputs are reused. The original collector still
copies only sealed lean/ sources to a fresh directory and runs all three checks.
The adapter, dependency source verification and mappings are inside its record.
"""
from pathlib import Path
import sys, os, json, hashlib, subprocess, shutil
R=Path('E:/数学总目录'); REPORT=R/'reports/QP01-publication-20261030'
sys.path.insert(0,str(R/'astra-math-workflow-v2'))
from mathflow import core, execution
for k in list(os.environ):
    if k.lower() in ('http_proxy','https_proxy','all_proxy'):os.environ.pop(k)
os.environ['NO_PROXY']='github.com,api.github.com'
gh=R/'tools/gh-v2.103.3/gh.exe'
lock=core.read_json(R/'outgoing/QP01-20261030-publication-licensed/payload/lean/lake-manifest.json')
source=Path('E:/lean4/mathlib4'); cache=R/'projects/verification-dependencies/qp01-mathlib435'
cache.parent.mkdir(parents=True,exist_ok=True)
# Never modify the installed/shared dependency directories.
if not (cache/'lake-manifest.json').exists():
    p=subprocess.run(['robocopy',str(source),str(cache),'/E','/XJ','/R:1','/W:1','/NFL','/NDL','/NJH','/NJS'],capture_output=True,timeout=600)
    assert p.returncode<8,p.returncode
rows=[]; packages=[]; normalized=[]; object_hashes={}
for pkg in lock['packages']:
    target=cache if pkg['name']=='mathlib' else cache/'.lake/packages'/pkg['name']
    url=pkg['url']; repo=url.removesuffix('.git').split('github.com/')[-1]
    command=[str(gh),'api',f"repos/{repo}/git/trees/{pkg['rev']}?recursive=1"]
    p=subprocess.run(command,capture_output=True,text=True,encoding='utf-8',timeout=60)
    assert p.returncode==0,p.stderr
    tree=json.loads(p.stdout);assert not tree.get('truncated')
    checked=[]
    for item in tree['tree']:
        rel=item['path']
        if item['type']!='blob' or not (rel.endswith(('.lean','.toml')) or rel in ('lean-toolchain','lake-manifest.json')):continue
        f=target/rel;assert f.is_file(),str(f)
        b=f.read_bytes();blob=hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()
        if blob!=item['sha']:
            canonical=b.replace(b'\r\n',b'\n')
            canonical_blob=hashlib.sha1(f'blob {len(canonical)}\0'.encode()+canonical).hexdigest()
            assert canonical_blob==item['sha'],f'Substantive pinned source difference: {pkg["name"]}/{rel}'
            stat=f.stat();f.write_bytes(canonical);os.utime(f,ns=(stat.st_atime_ns,stat.st_mtime_ns))
            normalized.append({'package':pkg['name'],'path':rel,'change':'CRLF to upstream LF only','before_sha256':hashlib.sha256(b).hexdigest(),'after_sha256':hashlib.sha256(canonical).hexdigest()})
            b=canonical;blob=canonical_blob
        assert blob==item['sha'],f'Pinned source differs: {pkg["name"]}/{rel}'
        installed=source/rel if pkg['name']=='mathlib' else source/'.lake/packages'/pkg['name']/rel
        checked.append({'path':rel,'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest(),'installed_source_sha256':core.file_hash(installed)})
    rows.append({'name':pkg['name'],'repo':repo,'revision':pkg['rev'],'source_files_verified':checked})
    known={i['path'] for i in tree['tree'] if i['type']=='blob'}
    extras=[]
    for f in target.rglob('*.lean'):
        rel=f.relative_to(target).as_posix()
        if '.lake' in Path(rel).parts or '.git' in Path(rel).parts:continue
        if rel not in known:extras.append(rel)
    assert not extras,f'Extra dependency sources: {pkg["name"]}: {extras}'
    for f in (target/'.lake/build/lib/lean').rglob('*'):
        if not f.is_file() or not f.name.endswith(('.olean','.olean.server','.olean.private')):continue
        rel=f.relative_to(target/'.lake/build/lib/lean').as_posix()
        assert rel.split('.olean',1)[0]+'.lean' in known,f'Extra dependency object: {pkg["name"]}/{rel}'
        object_hashes[str(f)]=core.file_hash(f)
    packages.append({'name':pkg['name'],'type':'path','dir':str(target),'inherited':pkg.get('inherited',False),'scope':pkg.get('scope',''),'configFile':pkg['configFile'],'manifestFile':pkg.get('manifestFile','lake-manifest.json')})
mapping={'version':'1.3.0','packagesDir':'.lake/packages','packages':packages,'name':'periodic_laguerre','lakeDir':'.lake'}
mapping_file=REPORT/'verified-package-overrides.json';core.write_json(mapping_file,mapping)
verification=REPORT/'verified-dependency-sources.json';core.write_json(verification,{'method':'GitHub exact commit tree and Git blob content hashes','dependencies':rows,'line_ending_restorations':normalized,'config_restoration':core.read_json(REPORT/'mathlib-lakefile-restoration.json'),'object_sha256':object_hashes,'shared_installation_modified':False,'extra_importable_source_and_object_check':'passed','cache_provenance':'E:/lean4/STATUS.md and mathlib-build10.log; historical local build, not independent current source rebuild'})
trusted=Path('C:/Users/王/.elan/toolchains/leanprover--lean4---v4.35.0/bin'); real_run=execution.run_job
def run_with_dependencies(device,cwd,command,threads,memory_gb,seconds,log):
    if Path(command[0]).resolve()==(trusted/'lake.exe').resolve():
        command[1:1]=['--packages='+str(mapping_file),'--old','--no-cache']
    record=Path(log).parent
    for sourcefile,name in [(mapping_file,'dependency-overrides.json'),(verification,'dependency-source-verification.json'),(Path(__file__),'collector-dependency-adapter.py')]:
        if not (record/name).exists():shutil.copyfile(sourcefile,record/name)
    result=real_run(device,cwd,command,threads,memory_gb,seconds,log)
    if any(Path(str(arg)).name.lower()=='leanchecker.exe' for arg in command):
        observed=set()
        for pkg in packages:
            for f in (Path(pkg['dir'])/'.lake/build/lib/lean').rglob('*'):
                if f.is_file() and f.name.endswith(('.olean','.olean.server','.olean.private')):observed.add(str(f))
        assert observed==set(object_hashes),'Dependency object path set changed during verification'
        assert all(core.file_hash(Path(f))==h for f,h in object_hashes.items()),'Dependency objects changed during verification'
        core.write_json(record/'dependency-object-stability.json',{'unchanged':True,'object_count':len(object_hashes)})
    return result
execution.run_job=run_with_dependencies
r=execution.check_lean(R/'hub','PKG-cceef00d1439606f40e59dfd',trusted/'lake.exe',trusted/'leanchecker.exe','AuditFinalQP01','PartitionLaguerre.main_classification_proved',R/'device',4,4,1200)
core.write_json(REPORT/'official-check-cached.json',r)
print(json.dumps({k:r.get(k) for k in ('check_id','passed','checker_passed','error')},ensure_ascii=False))
