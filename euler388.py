import tools
import math
from time import time

N = 10**10
sieve_limit = int(N**(2.0/3.0))
sqrt_N = int(1.2 * math.sqrt(N))

totient_sums = []
totient_sum_cache = {}

mu = []
mertens_list = []
mertens_cache = {}

def get_totient_sums(n):
    phi = tools.totient_sieve(n)
    sums = [0] * (n + 1)
    
    for i in range(1, n+1):
        sums[i] = sums[i - 1] + phi[i]
    
    return sums

def calc_totient_sum(n):
    if n <= sieve_limit:
        return totient_sums[n]
    else:
        if not n in totient_sum_cache:
            s = n * (n - 1) / 2
            loop_limit = int(math.sqrt(4*n + 1) - 1) / 2
            
            for i in range(2, loop_limit + 1):
                s -= calc_totient_sum(n / i)
            
            sqrt_n = int(math.sqrt(n))
            for i in range(2, sqrt_n + 1):
                s -= totient_sums[i] * (n/i - n/(i+1))
        
            totient_sum_cache[n] = s
        else:
            s = totient_sum_cache[n]
    return s

def totient_sum(n):
    return calc_totient_sum(n) + 1
          
def get_mobius_sums(n):
    mu = tools.mobius_sieve(n)
    sums = [0] * (n + 1)
    
    for i in range(1, n+1):
        sums[i] = sums[i - 1] + mu[i]
    
    return sums

def calc_mertens(n):
    if n <= sieve_limit:
        return mertens_list[n]
    else:
        if not n in mertens_cache:
            s, sqrt_n = 1, int(math.sqrt(n))
            loop_limit = n / (sqrt_n + 1)
            
            for i in range(2, loop_limit+1):
                s -= calc_mertens(n / i)
            
            for i in range(1, sqrt_n + 1):
                s -= mertens_list[i] * (n/i - n/(i+1))
        
            mertens_cache[n] = s
        else:
            s = mertens_cache[n]

    return s

def mertens(n):
    return calc_mertens(n) + 1

def calc_2D(n):
    return 2 * (totient_sum(n))

def f(n):
    global mu; s = 0
    sqrt_n = int(math.sqrt(n))
    lim = n / (sqrt_n + 1)
    
    for i in range(1, lim + 1):
        s += mu[i] * (n/i) * (n/i) * (n/i)
    
    for i in range(1, sqrt_n + 1):
        s += (i*i*i) * (mertens(n/i) - mertens(n/(i+1)))

    return s

def init(n):
    global N, mertens_list, sieve_limit, totient_sums, mu, sqrt_N
    
    N, sieve_limit = n, int(n**(2.0/3.0))
    totient_sums = get_totient_sums(sieve_limit)
    mertens_list = get_mobius_sums(sieve_limit)
    sqrt_N = int(1.1 * math.sqrt(N))
    mu = tools.mobius_sieve(sqrt_N)

def calc(N):
    t = time()
    init(N)
    ans = f(N) + 3 * (calc_2D(N))
    return ans, time() - t

print calc(N)
