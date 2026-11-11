using System;
using System.Collections.Generic;

// Four-bit encoding; all letters are in 1,...,10.
internal static class ShadowPairs
{
    private const int Limit = 10;
    private static readonly ulong[] Low = new ulong[Limit + 1];
    private static ulong Encode(string w)
    {
        ulong word = 0;
        for (int i = 0; i < w.Length; ++i) word |= (ulong)(w[i] - '0') << (4 * i);
        return word;
    }
    private static ulong Lift(ulong w, int n, int r)
    {
        ulong add = 0;
        for (int i = 0; i < n; ++i)
            if (((w >> (4 * i)) & 15) >= (ulong)r) add |= 1UL << (4 * i);
        return w + add;
    }
    private static void Insert(HashSet<ulong> set, ulong word, int n, int r)
    {
        for (int g = 0; g <= n; ++g)
        {
            ulong mask = Low[g];
            set.Add((word & mask) | ((ulong)r << (4 * g)) | ((word & ~mask) << 4));
        }
    }
    private static long[,] Shadows(string p)
    {
        int m = p.Length, b = 0;
        foreach (char c in p) b = Math.Max(b, c - '0');
        var previous = new HashSet<ulong>[Limit + 1];
        previous[b] = new HashSet<ulong> { Encode(p) };
        var counts = new long[Limit+1,Limit+1];
        counts[m,b] = 1;
        for (int n = m+1; n <= Limit; ++n)
        {
            var next = new HashSet<ulong>[Limit + 1];
            for (int k = b; k <= b+n-m; ++k)
            {
                var set = new HashSet<ulong>();
                if (previous[k] != null)
                    foreach (ulong word in previous[k])
                        for (int r = 1; r <= k; ++r) Insert(set,word,n-1,r);
                if (previous[k-1] != null)
                    foreach (ulong word in previous[k-1])
                        for (int r = 1; r <= k; ++r) Insert(set,Lift(word,n-1,r),n-1,r);
                counts[n,k] = set.Count;
                if (n < Limit) next[k] = set;
                previous[k-1] = null;
            }
            previous = next;
        }
        return counts;
    }
    private static long[,] Populations()
    {
        var table = new long[Limit+1,Limit+1];
        table[0,0] = 1;
        for (int n=1;n<=Limit;n++) for (int k=1;k<=n;k++)
            table[n,k] = k*(table[n-1,k]+table[n-1,k-1]);
        return table;
    }
    public static void Main()
    {
        for (int n=0;n<=Limit;n++) Low[n] = (1UL << (4*n))-1;
        var hosts = Populations();
        string[,] pairs = {{"11212","12121"},{"11223","11332"},{"12123","13232"},{"12234","12443"},
            {"13442","14233"},{"121123","122213"},{"112133","112321"},{"112323","113232"}};
        Console.WriteLine("p,q,n,A(p),A(q),delta,nonzero_layer_delta");
        for(int i=0;i<pairs.GetLength(0);i++)
        {
            var p=pairs[i,0]; var q=pairs[i,1];
            var left=Shadows(p); var right=Shadows(q);
            for(int n=0;n<=Limit;n++)
            {
                long a=0, b=0; var delta=new List<string>();
                for(int k=0;k<=n;k++)
                {
                    long x=hosts[n,k]-left[n,k],y=hosts[n,k]-right[n,k];
                    if(x<0 || y<0) throw new Exception("invalid host count");
                    a+=x;b+=y;
                    if(x!=y) delta.Add(k+":"+(x-y));
                }
                Console.WriteLine("{0},{1},{2},{3},{4},{5},{6}",p,q,n,a,b,a-b,string.Join(";",delta));
            }
            GC.Collect();
        }
    }
}