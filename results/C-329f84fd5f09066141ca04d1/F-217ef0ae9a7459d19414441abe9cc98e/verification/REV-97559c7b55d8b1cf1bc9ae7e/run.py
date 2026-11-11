import pathlib,subprocess,hashlib
for name in ['Independent','Census','ShadowPairs','ShortShadows']:
 print('source',name,hashlib.sha256(pathlib.Path(name+'.cs').read_bytes()).hexdigest(),flush=True)
 subprocess.run([r'C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe','/nologo','/optimize+','/platform:x64','/out:'+name+'.exe',name+'.cs'],check=True)
 subprocess.run([str(pathlib.Path(name+'.exe').resolve())],check=True)
