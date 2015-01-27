from math import sqrt
from tools import totient_sieve
from time import time

N = 99999999019
sieve_limit = N**(2.0/3.0)
phi, F_list = [], []
F_cache = {}

def init(n):
    global N, sieve_limit, phi, F_list, F_cache
    N, sieve_limit = n, int(n**(2.0/3.0))
    
    phi = totient_sieve(sieve_limit + 1)
    phi[1] = 1
    F_cache = {}
    
    F_list = [0] * len(phi)
    F_list[1] = 1
    for i in range(2, len(F_list)):
        F_list[i] = F_list[i-1] + (i * phi[i])
    

def consec_int_sum(n):
    return n * (n+1) / 2

def F(n):
    if n <= sieve_limit:
        return F_list[n]
    else:
        if not n in F_cache:
            s = (n * (n+1) * (2*n + 1)) / 6
            sqrt_n = int(sqrt(n))
            lim = n / (sqrt_n + 1)
            
            for i in range(2, lim + 1):
                s -= i * F(n / i)
            
            for i in range(1, sqrt_n + 1):
                s -= F_list[i] * (consec_int_sum(n/i) - consec_int_sum(n/(i+1)))
        
            F_cache[n] = s
        else:
            s = F_cache[n]

        return s

def S(n):
    global phi, F
    
    s, sqrt_n = 0, int(sqrt(n))
    lim = n / (sqrt_n + 1)
    
    for k in range(1, lim + 1):
        s += k * phi[k] * (n/k)
    
    for k in range(1, sqrt_n + 1):
        s += k * (F(n/k) - F(n/(k+1)))

    return s

def calc(n):
    t = time()
    init(n)
    return (n + S(n)) // 2, time() - t

print calc(N)
