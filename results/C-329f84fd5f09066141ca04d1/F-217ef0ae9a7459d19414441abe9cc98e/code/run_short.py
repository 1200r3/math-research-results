import os, sys, pathlib, subprocess, tempfile, hashlib
src=pathlib.Path(__file__).resolve().with_name('ShortShadows.cs')
compiler=pathlib.Path(os.environ['SystemRoot'])/'Microsoft.NET/Framework64/v4.0.30319/csc.exe'
print('Python '+sys.version.split()[0]+'; single-thread C#; source sha256 '+hashlib.sha256(src.read_bytes()).hexdigest(),flush=True)
with tempfile.TemporaryDirectory(dir=src.parent,prefix='shadow-run-') as name:
    exe=pathlib.Path(name)/'shadow.exe'
    subprocess.run([str(compiler),'/nologo','/optimize+','/target:exe','/platform:x64','/out:'+str(exe),str(src)],check=True)
    subprocess.run([str(exe)],check=True)
