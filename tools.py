import sys, os, random
from operator import mul, add, truediv, sub
from math import log10, sqrt, pi, e, ceil, floor, log, exp
from functools import *
from itertools import *
from fractions import gcd, Fraction
from time import time
from random import randint

sqs = [False] * 256
num_trials_mr = 30
max_double = 1.79e308
sqrt_two_pi = sqrt(2 * pi)

for i in range(256):
    sqs[(i * i) & 255] = True

def mod(a, b):
    if a >= 0 and a < b:
        return a
    return a % b

def is_square(n):
    if not sqs[n & 255]: return False
    x = sqrt(n)
    return x == int(x)

def lcm(a, b):
    return (a * b) / gcd(a, b)

def extended_gcd(a, b):
    x, y, u, v = 0, 1, 1, 0
    while a != 0:
        q, r = divmod(b, a)
        m, n = x - u * q,y - v * q
        b, a, x, y, u, v = a, r, u, v, m, n
    return b, y, x

def mod_inverse(a, mod):
    return extended_gcd(a, mod)[2]
        
def factorial(n):
    return reduce(mul, range(2, n + 1)) if n > 1 else 1

def is_prime_naive(n):
    if n < 2: return False
    if n == 2 or n == 3: return True
    if not n & 1: return False
    if not n % 3: return False
    if n < 9: return True
    sq_n = int(sqrt(n)) + 1
    for i in range(5, sq_n, 6):
        if not n % i or not n % (i + 2): return False
    return True

def prime_sieve(n):
    # http://stackoverflow.com/questions/2068372/fastest-way-to-list-all-primes
    # -below-n-in-python/3035188#3035188
    correction = (n % 6 > 1)
    n = {0: n, 1: n-1, 2: n+4, 3: n+3, 4: n+2, 5: n+1}[n % 6]
    sieve = [True] * (n // 3)
    sieve[0] = False
    limit = int(sqrt(n)) // 3 + 1
    for i in range(limit):
        if sieve[i]:
            k = 3 * i + 1 | 1
            sieve[((k * k) // 3) :: (k << 1)] = \
                      [False] * ((n // 6 - (k * k) // 6 - 1) // k + 1)
            sieve[(k * k + (k << 2) - \
                   (k << 1) * (i & 1)) // 3 :: (k << 1)] = \
                   [False] * ((n // 6 - (k * k + (k << 2) - \
                                         2 * k * (i & 1)) // 6 - 1) // k + 1)
    return [2, 3] + [3*i + 1 | 1 for i in range(1, n // 3 - correction) if sieve[i]]

def is_prime_fast(n):
    """
        http://mathworld.wolfram.com/StrongPseudoprime.html
        Zhang (2001, 2002, 2005, 2006, 2007) conjectured that
        """
    firstPrime = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, \
                  53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, \
                  109, 113, 127, 131, 137, 139]
    
    if n >= 10**36:
        # w = range(2, int(2*log(n)**2)) 
        w = range(2, int(logn*log(logn)/log(2)) ) 
    
    elif n >= 1543267864443420616877677640751301: w = firstPrime[:20]
    elif n >= 564132928021909221014087501701: w = firstPrime[:18]
    elif n >= 59276361075595573263446330101: w = firstPrime[:16]
    elif n >= 6003094289670105800312596501: w = firstPrime[:15]
    elif n >= 3317044064679887385961981: w = firstPrime[:14]
    elif n >= 318665857834031151167461: w = firstPrime[:13]
    elif n >= 3825123056546413051: w = firstPrime[:12]#[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    elif n >= 341550071728321: w = firstPrime[:9]#[2, 3, 5, 7, 11, 13, 17, 19, 23]
    elif n >= 3474749660383: w = firstPrime[:7]#[2, 3, 5, 7, 11, 13, 17]
    elif n >= 2152302898749: w = firstPrime[:6]#[2, 3, 5, 7, 11, 13]
    elif n >= 4759123141: w = firstPrime[:5]#[2, 3, 5, 7, 11]
    elif n >= 9006403: w = [2, 7, 61]
    elif n >= 489997:
        if n&1 and n%3 and n%5 and n%7 and n%11 and n%13 and n%17 and n%19\
        and n%23 and n%29 and n%31 and n%37 and n%41 and n%43 and n%47\
        and n%53 and n%59 and n%61 and n%67 and n%71 and n%73 and n%79\
        and n%83 and n%89 and n%97 and n%101:
            # Fermat 2, 3, 5, special remix
            hn = n>>1
            nm1 = n-1
            p = pow(2, hn, n)
            if (p==1 or p==nm1):
                p = pow(3, hn, n)
                if (p==1 or p==nm1):
                    p = pow(5, hn, n)
                    return (p==1 or p==nm1)
        return False
    elif n>=42799:
        # Fermat 2, 5
        return n&1 and n%3 and n%5 and n%7 and n%11 and n%13 and n%17\
        and n%19 and n%23 and n%29 and n%31 and n%37 and n%41 and n%43\
        and pow(2, n-1, n)==1 and pow(5, n-1, n)==1
    elif n>=841:
        # Fermat 2
        return n&1 and n%3 and n%5 and n%7 and n%11 and n%13 and n%17\
        and n%19 and n%23 and n%29 and n%31 and n%37 and n%41 and n%43\
        and n%47 and n%53 and n%59 and n%61 and n%67 and n%71 and n%73\
        and n%79 and n%83 and n%89 and n%97 and n%101 and n%103\
        and pow(2, n-1, n)==1
    elif n>=25:
        # divisions seules
        return n&1 and n%3 and n%5 and n%7\
        and n%11 and n%13 and n%17 and n%19 and n%23
    elif n>=4:
        return n&1 and n%3
    else:
        return n>1
    
    if not(n&1 and n%3 and n%5 and n%7 and n%11 and n%13 and n%17\
           and n%19 and n%23 and n%29 and n%31 and n%37 and n%41 and n%43\
           and n%47 and n%53 and n%59 and n%61 and n%67 and n%71 and n%73\
           and n%79 and n%83 and n%89): return False
    
    # Miller-Rabin
    s = 0
    d = n-1
    while not d&1:
        d>>=1
        s+=1
    for p in w:
        x = pow(p, d, n)
        if x == 1: continue
        for _ in range(s):
            if x+1 == n: break
            x = x*x%n
        else: return False
    return True


def is_prime(n):
    if n < 100000: return is_prime_naive(n)
    else: return is_prime_fast(n)

def trial_division(n):
    factors = [1, n]; sqrt_n = int(sqrt(n)) + 1
    start, step = (3, 2) if n & 1 == 1 else (2, 1)
    for i in range(start, sqrt_n, step):
        if n % i == 0:
            factors.append(i); factors.append(int(n/i))
    return list(sorted(factors))

primes = prime_sieve(25000)

def factorize(n):
    sn = int(sqrt(n))
    f = []
    for p in primes:
      if p > sn:
        if n > 1:
          f.append((n, 1))
          n = 1
        break
      i = 0
      while n % p == 0:
        n //= p
        i += 1
      if i > 0:
        f.append((p, i))
        sn = int(sqrt(n))
    if n > 1:
      big_divs = factorize_rho(n)
      if not big_divs: print (n, big_divs)
      f.extend(big_divs)
    return f

def merge_factorizations(f1, f2):
    f = []
    i = j = 0
    while i < len(f1) and j < len(f2):
      if f1[i][0] < f2[j][0]:
        f.append(f1[i])
        i += 1
      elif f1[i][0] > f2[j][0]:
        f.append(f2[j])
        j += 1
      else:
        f.append((f1[i][0], f1[i][1] + f2[j][1]))
        i += 1
        j += 1
    if i < len(f1):
      f.extend(f1[i:])
    elif j < len(f2):
      f.extend(f2[j:])
    return f

def factorize_rho(n):
    if is_prime_fast(n):
      return [(n, 1)]
    for i in range(len(primes) - 1, -1, -1):
        r, c, y = 1, primes[i], randint(1, n - 1)
        m, g, q, ys = randint(1, n - 1), 1, 1, y
        min_val, k = 0, 0
        while g == 1:
            x, k = y, 0
            for j in range(r):
                y = y*y + c
                if y > n: y %= n
            while k < r and g == 1:
                ys, min_val = y, min(m, r - k)
                for j in range(min_val):
                    y = y*y + c
                    if y > n : y %= n
                    q = q * abs(x - y)
                    if q > n: q %= n
                g = gcd(q, n)
                k += m
            r <<= 1
        if g == n:
           while True:
               ys = ys*ys + c
               if ys > n: ys %= n
               g = gcd(abs(x - ys), n)
               if g > 1: break
        if g != n:
            f1 = factorize_rho(g)
            f2 = factorize_rho(n/g)
            return merge_factorizations(f1, f2)
        else:
            # Try one more time - TODO: Improve this since it recurses
            # forever
            x = factorize_rho(n)
            return x

def divisors_with_prime_factors(f):
    d = 1; r = []
    p = [0] * len(f)
    while True:
        r.append(d)
        i = 0
        while i < len(f) and p[i] == f[i][1]:
            p[i] = 0
            d //= f[i][0] ** f[i][1]
            i += 1
        if i >= len(f): break
        p[i] += 1
        d *= f[i][0]
    return r

def divisors(n):
    f = factorize(n)
    return divisors_with_prime_factors(f)
