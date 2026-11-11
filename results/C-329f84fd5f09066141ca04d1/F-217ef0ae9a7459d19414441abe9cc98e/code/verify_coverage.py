from collections import defaultdict
from itertools import product
from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
E=HERE.parent/'evidence'

def fail_if(b,msg):
    if b: raise ValueError(msg)

def packed(m,b=None):
    return {''.join(w) for w in product('123456'[:m if b is None else b], repeat=m)
            if set(w)==set('123456'[:int(max(w))])}

def orbit(p):
    c=''.join(str(int(max(p))+1-int(x)) for x in p)
    return {p,p[::-1],c,c[::-1]}

def log(name):
    f=E/(name+'.log')
    r=json.loads((E/(name+'.log.result.json')).read_text(encoding='utf8'))
    fail_if(r['timed_out'] or r['returncode']!=0 or hashlib.sha256(f.read_bytes()).hexdigest()!=r['log_sha256'],f'invalid receipt {name}')
    return f.read_text(encoding='utf8').splitlines()

def unique_put(obj,key,val):
    fail_if(key in obj, f'duplicate count {key}')
    obj[key]=val

rows=json.loads((E/'word-class-rows.json').read_text(encoding='utf8'))
for m,key,npat,nclass in [(4,'4',75,16),(5,'5',541,116),(6,'6binary',63,18)]:
    expanded=[set().union(*(orbit(p) for p in row)) for row in rows[key]]
    p=packed(m,2 if m==6 else None)
    fail_if(len(rows[key])!=nclass or len(p)!=npat or set().union(*expanded)!=p or sum(map(len,expanded))!=npat,
            f'class coverage mismatch {key}')

census={4:{},5:{}}
for line in log('census'):
    if re.fullmatch(r'[45],(?:8|9),\d+,\d+',line):
        m,n,p,x=line.split(','); unique_put(census[int(m)],p,int(x))
shadow={}
for line in log('shadow'):
    if re.match(r'^\d{5,6},\d{5,6},',line):
        p,q,n,a,b,d,_=line.split(','); a=int(a); b=int(b)
        fail_if(a-b!=int(d),'invalid shadow difference')
        unique_put(shadow,(p,q,int(n)),(a,b))
joint={}
for line in log('joint'):
    if line.startswith('total,'):
        _,n,a,b,d=line.split(','); a=int(a); b=int(b)
        fail_if(a-b!=int(d),'invalid joint difference')
        unique_put(joint,int(n),(a,b))
for n in (9,10):
    fail_if(joint[n]!=shadow['11223','11332',n],'independent algorithms disagree')
short={}
for line in log('short'):
    if re.fullmatch(r'\d+,\d+,\d+',line):
        p,n,a=line.split(','); unique_put(short,(p,int(n)),int(a))

by_length={}
for m,n in ((4,8),(5,9)):
    rs=rows[str(m)]
    fail_if(set(census[m])!=packed(m),'census pattern coverage')
    by_count=defaultdict(list)
    for row in rs:
        vals={census[m][p] for rep in row for p in orbit(rep)}
        fail_if(len(vals)!=1,'class-count mismatch')
        by_count[vals.pop()].append(row[0])
    ties={k:v for k,v in by_count.items() if len(v)>1}
    target={394884:['1223','1332']} if m==4 else {
        6422046:['13442','14233'],6426616:['12234','12443'],6695989:['12123','13232'],
        6702104:['11223','11332'],6916076:['11212','12121']}
    fail_if(ties!=target,'collision list differs')
    witnesses=[]
    for count,(p,q) in sorted(ties.items()):
        if m==4:
            j=9; a,b=short[p,9],short[q,9]
        elif (p,q)==('11223','11332'):
            j=11; a,b=joint[11]
        else:
            j=10; a,b=shadow[p,q,10]
        fail_if(a==b,'class separation not proved')
        witnesses.append({'patterns':[p,q],'common_length':n,'common_count':count,'witness_length':j,'counts':[a,b]})
    by_length[str(m)]={'classes':len(rs),'baseline_host_length':n,'collisions':witnesses}

tail={}
for line in log('binary'):
    if re.fullmatch(r'\d+,\d+,\d+',line):
        p,n,a=line.split(','); unique_put(tail,(p,int(n)),int(a))
classes=defaultdict(list)
for row in rows['6binary']:
    p=row[0]; classes[tuple(short[p,n] for n in range(6,11))].append(p)
ties=[v for v in classes.values() if len(v)>1]
fail_if({frozenset(x) for x in ties}!={frozenset(('112112','121112')),frozenset(('111212','112121'))},'binary collision list')
out=[]
for p,q in sorted(ties):
    fail_if(tail[p,11]==tail[q,11],'binary class separation not proved')
    for x in (p,q):
        for n in range(6,11):
            fail_if(tail[x,n]!=short[x,n],'binary continuation disagrees with base counts')
    out.append({'patterns':[p,q],'witness_length':11,'counts':[tail[p,11],tail[q,11]]})
by_length['6binary']={'classes':len(rows['6binary']),'baseline_host_lengths':[6,7,8,9,10],'collisions':out}

def standard(w):
    rank={x:str(i) for i,x in enumerate(sorted(set(w)),1)}
    return ''.join(rank[x] for x in w)
from itertools import combinations
for m,reps,wanted in [(2,['11','12'],[6,4]),(3,['111','112','123'],[66,60,56])]:
    counts=[sum(not any(standard([w[i] for i in ix])==p for ix in combinations(range(m+1),m))
                for w in packed(m+1)) for p in reps]
    fail_if(counts!=wanted,'small length witness differs')
    by_length[str(m)]={'representatives':reps,'witness_length':m+1,'counts':counts}
print(json.dumps(by_length,indent=2))
