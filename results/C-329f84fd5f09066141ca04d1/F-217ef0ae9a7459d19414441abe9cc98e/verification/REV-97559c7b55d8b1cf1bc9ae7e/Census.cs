using System;
using System.Collections.Generic;
internal static class Census
{
    private static int N,M,K,All,Epoch;
    private static int[] Digit, KeyToId, Hit;
    private static long[] Contain;
    private static int[][] Columns;
    private static List<int> Patterns;
    private static Dictionary<int,int> Id;
    private static int[] Popcount = new int[1<<12];

    private static void Lookup(int depth,int code,int mask)
    {
        if(depth==M)
        {
            int p=0;
            for(int i=0;i<M;i++)
            {
                int v=(code>>(4*i))&15;
                p |= (1+Popcount[mask&((1<<v)-1)])<<(4*i);
            }
            int index;
            if(!Id.TryGetValue(p,out index))
            {
                index=Patterns.Count;
                Patterns.Add(p);
                Id.Add(p,index);
            }
            KeyToId[code]=index;
            return;
        }
        for(int v=1;v<=N;v++) Lookup(depth+1,code|(v<<(4*depth)),mask|(1<<v));
    }
    private static void ColumnsRec(int depth,int start,int[] selected,List<int[]> cs)
    {
        if(depth==M) { cs.Add((int[])selected.Clone()); return; }
        for(int i=start;i<=N-(M-depth);i++)
        { selected[depth]=i; ColumnsRec(depth+1,i+1,selected,cs); }
    }
    private static void Visit(int i,int seen,int missing)
    {
        if(i==N)
        {
            if(missing!=0) throw new Exception("non-packed host");
            int stamp=++Epoch;
            var w=Digit;
            var a=Columns[0];var b=Columns[1];var c=Columns[2];var d=Columns[3];
            if(M==4)
            {
                for(int j=0;j<a.Length;j++)
                {
                    int id=KeyToId[w[a[j]]|(w[b[j]]<<4)|(w[c[j]]<<8)|(w[d[j]]<<12)];
                    if(Hit[id]!=stamp){Hit[id]=stamp;Contain[id]++;}
                }
            }
            else
            {
                var e=Columns[4];
                for(int j=0;j<a.Length;j++)
                {
                    int id=KeyToId[w[a[j]]|(w[b[j]]<<4)|(w[c[j]]<<8)|(w[d[j]]<<12)|(w[e[j]]<<16)];
                    if(Hit[id]!=stamp){Hit[id]=stamp;Contain[id]++;}
                }
            }
            return;
        }
        int choices = N-i == missing ? All^seen : All;
        for(int x=1;x<=K;x++)
        {
            int bit=1<<x;
            if((choices&bit)==0) continue;
            Digit[i]=x; Visit(i+1,seen|bit,missing-((seen&bit)==0?1:0));
        }
    }
    private static void Run(int m,int n)
    {
        M=m;N=n;Epoch=0;Digit=new int[N];
        KeyToId=new int[1<<(4*M)];Patterns=new List<int>();Id=new Dictionary<int,int>();
        Lookup(0,0,0); Hit=new int[Patterns.Count];Contain=new long[Patterns.Count];
        var list=new List<int[]>();
        ColumnsRec(0,0,new int[M],list);
        Columns=new int[M][];
        for(int i=0;i<M;i++)
        {
            Columns[i]=new int[list.Count];
            for(int j=0;j<list.Count;j++) Columns[i][j]=list[j][i];
        }
        for(K=1;K<=N;K++){All=(1<<(K+1))-2; Visit(0,0,K);}
        var expected=new long[N+1,N+1];
        expected[0,0]=1;
        for(int i=1;i<=N;i++) for(int j=1;j<=i;j++)
            expected[i,j]=j*(expected[i-1,j]+expected[i-1,j-1]);
        long total=0;for(int j=1;j<=N;j++) total+=expected[N,j];
        if(total!=Epoch) throw new Exception("wrong population");
        for(int id=0;id<Patterns.Count;id++)
        {
            int code=Patterns[id];var p=new char[M];
            for(int i=0;i<M;i++) p[i]=(char)('0'+((code>>(4*i))&15));
            Console.WriteLine("{0},{1},{2},{3}",M,N,new string(p),total-Contain[id]);
        }
    }
    public static void Main()
    {
        for(int i=1;i<Popcount.Length;i++) Popcount[i]=Popcount[i>>1]+(i&1);
        Console.WriteLine("m,n,pattern,avoidance");
        Run(4,8);
        Run(5,9);
    }
}