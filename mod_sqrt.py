from tools import mod, mod_inverse, factorize, gcd
from time import time

def mod(a, b):
    if a >= 0 and a < b:
        return a
    return a % b

def legendre_symbol(n, p):
    x = pow(n, (p - 1) >> 1, p)
    return -1 if x == p - 1 else x

# Returns a square root mod a prime with the
# Tonelli-Shanks algorithm
def tonelli_shanks(n, p):
    if n == 0:
        return 0
    elif n < 0:
        n = mod(n, p)
    # Simple cases
    if p == 2:
        return n
    elif legendre_symbol(n, p) != 1:
        return -1
    elif (p & 3) == 3:
        return pow(n, (p + 1) >> 2, p)
    elif (p & 7) == 5:
        c = pow(n << 1, (p - 5) >> 3, p)
        i = mod(mod(c * c, p) * (n << 1), p)
        return mod(mod(n * c, p) * (i - 1), p)
    
    # Extract factors of 2 
    s, e = p - 1, 0
    while (s & 3) == 0:
        s >>= 2
        e += 2
    if (s & 1) == 0:
        s >>= 1
        e += 1
        
    # Find least non-quadratic residue of p
    a = 2
    while legendre_symbol(a, p) != -1:
        a += 1
    x = pow(n, (s + 1) >> 1, p)
    b = pow(n, s, p)
    g = pow(a, s, p)
    r = e
    while True:
        t, m = b, 0
        while t != 1:
            m += 1
            t = mod(t * t, p)
        if m == 0:
            return x
        g = pow(g, 1 << (r - m - 1), p)
        x = mod(x * g, p)
        g = mod(g * g, p)
        b = mod(b * g, p)
        r = m

# Returns a square root mod a prime power through
# iterative lifting via Hensel's lemma i.e. it
# returns a y such thaty^2 = x (mod p^pow) where
# x % p != 0
def hensel_lift(x, p, pow):
    if p == 2:
        if pow == 1:
            return [1]
        elif pow == 2:
            return [1] if (x & 3) == 1 else None
        if (x & 7) != 1:
            return None
        
        # 1 has 2 roots: (1, 3) mod 8
        sol = [1, 3]
        for pos in range(len(sol)):
            y, p_pow, temp_pow = sol[pos], 8, pow
            i, temp = 0, 0
            for temp_pow in range(3, pow):
                temp = (y*y - x) >> temp_pow
                i = 1 if (temp & 1) == 1 else 0
                y += i << (temp_pow - 1)
            sol[pos] = y
        return sol
    else:
        y = tonelli_shanks(mod(x, p), p)
        # No square root mod p
        if y == -1: return None
        p_pow, temp, deriv, t = p, 0, 0, 0
        for _ in range(pow, 1, -1):
            # Lift y^2 - x over p^pow
            temp = (x - y*y) / p_pow
            deriv = y * 2
            if mod(deriv, p) == 0:
                return None
            t = mod(mod_inverse(deriv, p) * temp, p)
            y += t * p_pow
            p_pow *= p
        return [y]

# Returns a square root of mod a prime power i.e.
# returns a y such that y^2 = x (mod p^n).
# Adapted from Sympy's version of the same. 
def sqrt_mod_prime_pow(x, p, n):
    if x % p:
        return hensel_lift(x, p, n)
    else:
        res = []
        pn = pow(p, n)
        y = mod(x, pn)
        # Case 1
        if y == 0:
            m, i = n >> 1, 0
            pm = pow(p, m + 1) if (n & 1) == 1 else pow(p, m)
            while i < pn:
                res.append(i)
                i += pm
            return res
        else:
            g = gcd(x, pn)
            r = 0
            # Extract factors of the prime from the gcd
            while g % p == 0:
                g /= p
                r += 1
            if (r & 1) == 1:
                return None
            m = r >> 1
            x1 = x >> r
            if p == 2:
                # Case 2a
                if n - r == 1:
                    pmn1 = 1 << (n - m + 1)
                    pm1 = 1 << (m + 1)
                    k, i = pm1 << 1, pm1 >> 1
                    while i < pmn1:
                        j = i
                        while j < pn:
                            res.append(j)
                            j += k
                        i += pm1
                # Case 2b
                elif n - r == 2:
                    res1 = hensel_lift(x1, p, n - r)
                    if res1 is None:
                        return None
                    pnm, s = 1 << (n - m), set([])
                    for r in res1:
                        i = 0
                        while i < pn:
                            x = (r << m) + i
                            s.add(x)
                            i += pnm
                    res = list(s)
                # Case 2c
                else:
                    res1 = hensel_lift(x1, p, n - r)
                    if res1 is None:
                        return None
                    pnm1, s = 1 << (n - m - 1),  set([])
                    for r in res1:
                        i = 0
                        while i < pn:
                            x = mod((r << m) + i, pn)
                            s.add(x)
                            i += pnm1
                    res = list(s)
            # case 3
            else:
                m = r >> 1
                x1 = x // pow(p, r)
                res1 = hensel_lift(x1, p, n - r)
                if res1 is None:
                    return None
                res1 = res1[0]
                pm = pow(p, m)
                pnr = pow(p, n - r)
                pnm = pow(p, n - m)
                i = 0
                while i < pnm:
                    x = mod(res1 + i, pn)
                    res.append(x * pm)
                    i += pnr
            return res               
                

# A basic recursive implementation of the Chinese Remainder
# theorem
def solve_crt(curr, p_pows, smp, inv, ndf, \
              pos, n, sqrts):
    try:
        solve_crt(curr + (smp[pos] * inv[pos] * \
                         ndf[pos]), p_pows, smp, inv,\
                  ndf, pos + 1, n, sqrts)
        solve_crt(curr + ((p_pows[pos] - smp[pos]) * \
                         inv[pos] * ndf[pos]), p_pows,\
                  smp, inv, ndf, pos + 1, n, sqrts)
    except:
        sqrts.append(mod(curr, n))

# Recursively uses the CRT on all possible residue combinations to
# construct all the square roots
def solve_recursive(curr, p_pows, smps, inv, ndf, pos, n, sqrts):
    if pos < len(smps):
        for i in smps[pos]:
            s = curr + [i]
            solve_recursive(s, p_pows, smps, inv, \
                            ndf, pos + 1, n, sqrts)
    else:
        solve_crt(0, p_pows, curr, inv, ndf, 0, n, sqrts)
        return 

# Returns a new list which contains the minimum of
# every pair (x, y) in l such that x + y = n or
# (x + -x) = 0 (mod n).Since x^2 = (-x)^2 (mod n),
# the solve_crt method takes care of it. Including -x
# (mod n) in l is wasteful.
def filter_list(l, n):
   new_list = []
   for i in range(len(l) >> 1):
       if l[i] + l[len(l) - i - 1] == n:
           new_list.append(l[i])
       else:
            new_list.append(l[i])
            new_list.append(l[len(l) - 1 - i])
   if (len(l) & 1) == 1:
        new_list.append(l[len(l) >> 1])
   return new_list
    
# Returns a list of solutions to y^2 = x (mod n) where fact_n
# is the prime factorization of n
def mod_sqrt_pf(x, n, fact_n):
    p_pows, inv, ndf =[], [], []
    smps, sqrts = [], []
    for pfp in fact_n:
        p_pows.append(pow(pfp[0], pfp[1]))
        ndf.append(n / p_pows[-1])
        inv.append(mod_inverse(ndf[-1], p_pows[-1]))
        temp = sqrt_mod_prime_pow(x, pfp[0], pfp[1])
        if temp is None:
            return []
        smps.append(temp)
    solve_recursive([], p_pows, smps, inv, ndf, 0, n, sqrts)
    sqrts = list(sorted(set(sqrts)))
    return sqrts

# Returns a list of solutions to y^2 = x (mod n)
def mod_sqrt(x, n, fact_n = []):
    if x == 0 or n == 0:
        return [0]
    elif n == 1:
        if x == 0:
            return [0]
        else:
            return [1]
    if not fact_n:
        fact_n = factorize(n)
    return mod_sqrt_pf(x, n, fact_n)
