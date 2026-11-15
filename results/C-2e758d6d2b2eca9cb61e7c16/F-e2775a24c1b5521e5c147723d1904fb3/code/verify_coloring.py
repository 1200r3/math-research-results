"""Exhaustive verifier for the finite triangular-lattice coloring result."""
from collections import deque
from itertools import combinations
from math import comb
from pathlib import Path
import json

def geometry(n):
    points = [(i, j) for i in range(n) for j in range(n-i)]
    index = {p: i for i, p in enumerate(points)}
    edges = set()
    for (a, b), (c, d) in combinations(points, 2):
        u, v = c-a, d-b
        for p in [(a-v, b+u+v), (a+u+v, b-u)]:
            if p in index:
                edges.add(tuple(sorted((index[a,b], index[c,d], index[p]))))
    assert len(edges) == comb(n+2, 4)
    return points, sorted(edges)

def three(n):
    points, edges = geometry(n)
    pairs = [[] for p in points]
    for a,b,c in edges:
        pairs[a].append((b,c))
        pairs[b].append((a,c))
        pairs[c].append((a,b))
    nodes=conflicts=models=0
    def visit(ds, pending):
        nonlocal nodes,conflicts,models
        nodes += 1
        todo=deque([pending])
        while todo:
            i=todo.popleft()
            color=ds[i]
            for a,b in pairs[i]:
                if ds[a] != color:
                    if ds[b] != color:
                        continue
                    a,b=b,a
                if ds[b]&color:
                    ds[b]^=color
                    if not ds[b]:
                        conflicts += 1
                        return
                    if ds[b].bit_count()==1:
                        todo.append(b)
        keys=[(d.bit_count(),-len(pairs[i]),i) for i,d in enumerate(ds) if d.bit_count()>1]
        if not keys:
            assert all(not (ds[a]==ds[b]==ds[c]) for a,b,c in edges)
            models += 1
            return
        _,_,i=min(keys)
        for k in (1,2,4):
            if ds[i]&k:
                branch=ds.copy()
                branch[i]=k
                visit(branch,i)
    visit([1]+[7]*(len(points)-1),0)
    return dict(points=len(points),triangles=len(edges),nodes=nodes,conflicts=conflicts,models_with_origin_color_0=models)

def main():
    result={str(n):three(n) for n in (8,9)}
    assert result['8']['models_with_origin_color_0']==216
    assert result['9']['models_with_origin_color_0']==0
    data_dir=Path(__file__).resolve().parent.parent/'data'
    source=json.loads((data_dir/'c02_fourcolor_witnesses.json').read_text(encoding='utf-8'))
    result['four_color']={}
    for n in range(9,13):
        points, edges=geometry(n)
        witness=source[f'{n}_4']['witness']
        assert set(witness)=={str(p) for p in points}
        colors=[witness[str(p)] for p in points]
        assert {type(x) for x in colors}=={int} and set(colors)==set(range(4))
        count=sum(colors[a]==colors[b]==colors[c] for a,b,c in edges)
        assert count==0
        result['four_color'][str(n)]={'points':len(points),'triangles':len(edges),'monochromatic':count}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':
    main()

