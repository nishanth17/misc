from tools import spf_sieve
from time import time

N = 10**6
mul = 1234567890
spf = spf_sieve(N)

# Returns a list of the prime facirs of n
def gen_prime_factors(n):
    factors = []
    while n != 1:
        pf = spf[n]
        while n % pf == 0:
            n /= pf
        factors.append(pf)
    return factors

# Returns the power of p in n!
def pow_in_factorial(n, p):
    s = 0
    while n != 0:
        n /= p
        s += n
    return s

# Returns the smallest n such that p^target divides n!
def min_n(p, target):
    lo = int(float((p-1) * target) / p + 1) * p
    
    while True:
        if pow_in_factorial(lo, p) >= target:
            return lo
        lo += p

def solve():
    t = time()
    min_n_val, total = 0, 0
    
    for i in range(2, N + 1):
        pfs = gen_prime_factors(i)

        for p in pfs:
            s = pow_in_factorial(i, p)
            x = min_n(p, mul * s)

            if x > min_n_val:
                min_n_val = x

        if i >= 10:
            total = total + min_n_val

    return total, time() - t

print solve()
