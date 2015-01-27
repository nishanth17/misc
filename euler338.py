import math
from time import time
from fractions import Fraction

###############################
# Really small cases - O(n^3) #
###############################

def G_cache(n):
    cache = [[] for _ in range(n)]
    for w in range(1, n+1):
        for h in range(1, w+1):
            for d in range(2, h+1):
                if h % d == 0 and w % (d-1) == 0:
                    cache[d-1].append((w, h))
    return cache

def print_cache(n):
    cache = G_cache(n)
    for d in range(1, len(cache)):
        print (d, d+1), sorted(cache[d], key = lambda x : x[0])

def cache_length(n):
    cache = G_cache(n)
    total_len = 0
    for d in range(1, len(cache)):
        total_len += len(cache[d])
    print "Total: ", total_len

# (w, h) -> (h, w)
def print_self_congruences(w):
    for h in range(1, w+1):
        for d in range(2, w+1):
            if  w % d == 0 and h % (d-1) == 0:
                new_w, new_h = w/d * (d-1), h/(d-1) * d
                if new_w == h and new_h == w:
                    print d

# (w, h) -> (w', h'), (w, h) -> (h', w')
def print_congruences(n):
    print "\nPrinting congruences for", n,  "\n"
    cache = {}
    for w in range(1, n+1):
        s = {}
        for h in range(1, w+1):
            for d in range(1, w+1):
                if  d > 1 and w % d == 0 and h % (d-1) == 0:
                    new_w, new_h = w/d * (d-1), h/(d-1) * d
                    if (new_h, new_w) in s:
                        #print (w, h), (d, d-1), s[(new_h, new_w)]
                        if not (d, d-1) in cache:
                            cache[(d, d-1)] = [s[(new_h, new_w)]]
                        else:
                            cache[(d, d-1)].append(s[(new_h, new_w)])
                    else:
                        s[(new_w, new_h)] = (d, d-1)
                if w % d == 0 and h % (d+1) == 0:
                    new_w, new_h = w/d * (d+1), h/(d+1) * d
                    if (new_h, new_w) in s:
                        #print (w, h), (d, d+1), s[(new_h, new_w)]
                        if not (d, d+1) in cache:
                            cache[(d, d+1)] = [s[(new_h, new_w)]]
                        else:
                            cache[(d, d+1)].append(s[(new_h, new_w)])
                    else:
                        s[(new_w, new_h)] = (d, d+1)

    print "Minus one"
    for key in list(sorted(cache))[::2]:
        print key, sorted(list(cache[key]))

    print "\nPlus one"
    for key in list(sorted(cache))[1::2]:
        print key, sorted(list(cache[key]))


###############################
# Small cases - O(n * log(n)) #
###############################

def G1_slow(n):
    t = time()
    s = 0
    for d in range(1, n+1):
        for w in range(d+1, n+1, d+1):
            s += w / d
    return s, time() - t

def G2_slow(n):
    t = time()
    s = 0
    for d in range(2, n/2 + 2):
        for w in range(2*d - 2, n+1, d-1):
            s += w / d
    return s, time() - t

def G3_slow(n):
    t = time()
    s = 0
    for i in range(2, n+1):
        s += n / i
    return s, time() - t

def G_slow(n):
    t = time()
    return G1_slow(n)[0] + G2_slow(n)[0] - G3_slow(n)[0], time() - t

#####################
# Utility Functions #
#####################

# Returns sum(i, i = 1 to n) = n*(n+1)/2
def consec_int_sum(n):
    return n * (n+1) / 2

# Returns sum(i/d - floor(i/d), i = 1 to n)
def gain(n, d):
    num_cycles, mod = divmod(n, d)
    gain = Fraction(d-1, 2) * num_cycles
    gain += Fraction(mod * (mod+1), (2*d))
    return gain

###################################################################
# Large cases - O(sqrt(n)) - these seem to be really really close #
###################################################################

def f1(n):
    s, sqrt_n = 0, int(math.sqrt(n))
    loop_limit = n / (sqrt_n + 1)
    for i in range(2, loop_limit + 1):
        s += n/i * (n/i + 1)
    for i in range(1, sqrt_n+1):
        s += i * (i+1) * (n/i - n/(i+1))
    return s

def f2(n):
    s, sqrt_n = 0, int(math.sqrt(n))
    loop_limit = n / (sqrt_n + 1)
    for i in range(1, sqrt_n + 1):
        s += n/i * (n/i + 1)
    for i in range(3, loop_limit + 1):
        s += i * (i+1) * (n/i - n/(i+1))
    return s + (6 * (n/2 - n/3))

# w|d, h|(d-1) - relatively straightforward
def G1(n):
    t = time()
    s = f1(n)/2
    lim = int((math.sqrt(4*n + 1) - 1) / 2)
    
    for d in range(1, lim + 1):
        x = n/(d+1)
        # Compensate for fractional gain from exact division
        temp = Fraction(consec_int_sum(x) - consec_int_sum(d-1), d)
        temp -= gain(x - d + 1, d)
        s += int(math.ceil(temp))
    
    return s, time() - t

# w|d, h|(d+1) - annoying as hell
def G2(n):
    t = time()
    s = f2(n)/2 - n/2
    lim = int((math.sqrt(4*n + 1) + 1) / 2)
    lim1 = n / (int(math.sqrt(n)) + 1)
 
    for d in range(2, lim + 1):
        x = n/(d-1)
        # Compensate for fractional gain from exact division
        temp = Fraction(consec_int_sum(x) - consec_int_sum(d-1), d)
        temp -= gain(x - d + 1, d)
        s -= int(math.ceil(temp))
        s -= (x/d) * (d - 1) + (x % d) - 1

    # Note that floor division doesn't distribute over
    # subtraction. Compensate for it. 
    s -= n/2 - n/3
    start = lim if n / lim1 != lim else lim1
    for i in range(start, 2, -1):
        s -= (i - 1) * (n/i - n/(i+1))
    
    return s, time() - t

# (w, h) -> (h, w) - exclude these since they aren't distinct 
def G3(n):
    t = time()
    s, sqrt_n = 0, int(math.sqrt(n))
    loop_limit = n / (sqrt_n + 1)
    for i in range(1, loop_limit + 1):
        s += n/i
    for i in range(1, sqrt_n + 1):
        s += i * (n/i - n/(i+1))
    return s - n, time() - t

def G(n):
    t = time()
    return G1(n)[0] + G2(n)[0] - G3(n)[0], time() - t

#########
# Tests #
#########

def test(n):
    return 2 == 2

print G1_slow(10**10)
print G1(10**10)

