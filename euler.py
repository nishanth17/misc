from tools import *
import diophantine
from memoized import memoized
import mod_sqrt
from collections import deque
     
""" The efficient approach to this took a while to find."""
def euler_157(n = 9):
  t = time()

  # Returns all the factors of 10**n
  def factors_25(n):
    a = []
    for i in range(n + 1):
      for j in range(n + 1):
        a.append((2**i * 5**j))
    return a
    
  def count_solns(n):
    num = 10**n
    func = lambda x : num + int(num / x)
    count = sum(map(number_of_divisors, map(func, factors_25(n))))
    for i in range(1, n+1):
      for j in range(1, n+1):
        count += number_of_divisors(int((num / 2**i) + (num / 5**j)))
    return count
    
  return sum(map(count_solns, range(1, n+1))), time() - t
  
""" This was stupidly easy. """
def euler_207(s = 12345):
  t = time()
  denominator, j = s, 1
  frac = 1 / denominator
  j, pow2_j = 1, 2
  while j / pow2_j > frac:
    j += 1
    pow2_j <<= 1    
  n = (j - 1) * denominator
  return (n + 1) * (n + 2), time() - t

""" This was really easy. A basic binary search. """
def euler_235():
  t = time()
  limit, target, n = 10**(-13), 6 * pow(10, 11), 5000
  lo, hi = 1, 1.1
  
  while hi - lo > limit:
    mid = (hi + lo) / 2
    s_mid = abs(sum((900 - 3*k) * mid**(k - 1) for k in range(1, n+1)))
    if s_mid > target: hi = mid
    else: lo = mid
    
  return round(hi, 13), time() - t

""" Binary circles. This is relatively straightforward. """
def euler_265(n = 5):
  t = time()
  N = 1 << n
  mask = N - 1
  used_vals = [False] * N
  
  def count(num, pos):
    last_n_digits, s = num & mask, 0
    if used_vals[last_n_digits]: return 0
    used_vals[last_n_digits] = True
    
    if pos == N:
      flag, temp = True, last_n_digits
      # Check last (n - 1) digits
      for i in range(n - 1):
        temp = (temp << 1) & mask
        if used_vals[temp]:
          flag = False
          break 
      if flag:
        s += num        
    else:
      s += count(num << 1, pos + 1)
      s += count((num << 1) + 1, pos + 1)
      
    used_vals[last_n_digits] = False
    return s
  
  s = count(0, n)
  return s, time() - t

""" Note that a^2 + b^2 = n can be solved with either the Hermite-Serret 
# alogrithm or Cornacchia's algorithm. It turns out that brute force is
# feasible with PyPy.
# Answer: 2032447591196869022
# Time: 85s (in PyPy) """
def euler_273():
    t = time()
    limit, s = 150, 0
    primes = list(filter(lambda x : (x - 1) & 3 == 0, prime_sieve(limit)))
    
    def dfs(n, fact_n, primes, pos):
        s = 0
        a = diophantine.cornacchia_dm(1, n, fact_n)
        for i in a:
            s += min(i[0], i[1])
        for i in range(pos, len(primes)):
            s += dfs(n * primes[i], fact_n + [(primes[i], 1)], primes, i + 1)
        return s
    
    for i in range(len(primes)):
        s += dfs(primes[i], [(primes[i], 1)], primes, i + 1)
        
    return s, time() - t

""" This is pretty easy. If f(n) is the number of ways that no chip has
# more than n defects, the answer required = 1 - (f(1)+f(2))/n**k.
# The only caveat is dealing with large binomial coefficients which is
# easily overcome by using logarithms and exponentiating the final
# answer. 
# Answer: 0.7311720251
# Time: 0.015 s """
def euler_307(n = 10**6, k = 2 * 10**4):     
  t, log_2 = time(), log(2)

  # Account for f(1)
  accum = 0
  for i in range(n-k+1, n+1):
    accum += log(i)
  
  log_total = k * log(n)
  prob = exp(accum - log_total)
  
  # Account for f(2)
  for i in range(1, k//2 + 1):
    accum += log(k - 2*i + 2) + log(k - 2*i + 1) - log_2 -\
             log(i) - log(n-k+i)
    prob += exp(accum - log_total)

  return  1 - prob, time() - t

""" This is really easy with some research.
    # It turns out that M(n) = n(n+2) and all you need to solve
    # is x(x+2) = (y/2)(y+1) """
def euler_321():
    t = time()
    sols = set([])
    
    def gen_solutions(x, y):
        count = 0
        while len(sols) < 60 and count < 40:
            if x > 0:
                sols.add(x)
            temp_x = 3*x + 2*y + 3
            temp_y = 4*x + 3*y + 5
            x, y = temp_x, temp_y
            count += 1
    
    gen_solutions(0, 0)
    gen_solutions(0, -1)
    return sum(sorted(list(sols))[: 40]), time() - t

""" This was dead easy. """
def euler_346():
  t = time()
  limit = 10**12
  reps = set([])
  loop_limit = int(sqrt(limit))
  
  for b in range(2, loop_limit):
    n = 3    
    while True:
      r = (b**n - 1) // (b - 1)
      if r >= limit: break
      reps.add(r)
      n += 1
      
  return sum(reps) + 1, time() - t

""" P(1, n) = n/2 * (n+1)
# P(2n, 1) = 2n^2 
# P(2n+1, 1) = 2n^2 + 2n
# [P(f, n) - P(f, n-1)] - [P(f, n-2), P(f, n-3)] = 2
# P(2n+1, 2) - P(2n+1, 1) = 1
# P(2n, 2) - P(2n, 1) = 4n + 1
# P(2n+1, 3) - P(2n+1, 2) = 4n + 2
# P(2n, 3) - P(2n, 2) = 2 

TODO: Finish this later """
def euler_359(n = 100, arg = 0):
  floors = [[], [1]]
  
  for i in range(2, n+1):
    l,flag = len(floors), False
    for j in range(1, l):
      if is_square(floors[j][-1] + i):
        floors[j].append(i)
        flag = True
    if not flag:
      new_floor = [i]
      floors.append(new_floor)

  def print_floors():
    for i in range(1, len(floors)):
      print (str(i) + ": ", floors[i])

  def print_differences():
    for i in range(1, len(floors)):
      if len(floors[i]) > 1:
        print (str(i) + ": ", [floors[i][j] - floors[i][j-1] \
                              for j in range(1, len(floors[i]))])
  if arg == 0:
    print_floors()
  else:
    print_differences()
              

""" By Heron's formula , we find that the area 'a' satisfies 4a^2 = b^2
# + c^2 + (bc)^2. Since the left hand side is even, the only
# possibility is that both b and c are even. Plugging in b=2b and c=2c
# yields a^2 - (1+4b^2)c^2 = b^2 which is a generalized version of
# Pell's equation of the form x^2 - dy^2 = n. Now just iterate over
# all the possible values of b and add all valid solutions.
# Answer: 2919133642971
# Time: 195.90s (in PyPy) """
def euler_390(max_a = 10**6):
  t = time()
  max_a2 = max_a * max_a
  max_b = int((4*max_a2 - 3)**0.25 - 1) / 2
  total = 0; s = set()
  for b in range(1, max_b+1):
    b2 = b * b
    sols = diophantine.pell_dn(1 + 4*b2, b2, max_a)
    for a, c in sols:
      if a != b:
        s.add(a)
  return sum(s), time() - t

# THis was pretty easy.
def euler_435():
  t = time()
  n, m, l = 10**15, factorial(15), 100
  def F(x, n, m):
    denom = x * x + x - 1
    m *= denom
    f_n1 = fib_mod(n + 1, m)
    f_n = fib_mod(n, m)
    x_n1 = pow(x, n + 1, m)
    x_n2 = mod(x_n1 * x, m)
    num = mod(f_n1 * x_n1 + f_n * x_n2 - x, m)
    return num // denom
  return sum(F(i, n, m) for i in range(1, 101)) % m, time() - t

""" This is dead easy. Solve x^2 = 1 (mod n) for all 3 <= n <= 2 * 10^7
# and return the sum of the second largest solution of each (n-1 is
# the largest solution). 
# Answer: 153651073760956
# Time: 170s (in PyPy) """
def euler_451():
  t = time()
  limit = 2 * 10**7
  spf = spf_sieve(limit)
    
  def factorize_spf(n):
    factors = []
    while n != 1:
      count, pf = 0, spf[n]
      while n % pf == 0:
        n /= pf
        count += 1
      factors.append((pf, count))
    return factors
    
  s = 0
  for i in range(3, limit + 1):
    if i % 1000000 == 0:
      print (i, time() - t)
    s += mod_sqrt_pf(1, i, factorize_spf(i))[-2]
    
  return s, time() - t

""" This is stupidly easy. n^2 - 3n - 1 = 0 (mod p^2) implies that
# n = (3 + sqrt(13)) / 2 (mod p^2). Find the smallest n that
# satisfies the equation above for each prime and add them up.
# Answer: 264778712679397063
# Time: 14.41s """
def euler_457(l = 10**6):
  t = time()
  
  s, primes = 0, prime_sieve(l)
  for i in range(1, len(primes)):
    p = primes[i]
    p2 = p * p
    roots = mod_sqrt.mod_sqrt(13, p2, [(p ,2)])
    if not roots:
      continue
    
    min_n = float("inf")
    half = mod_inverse(2, p2)
    for r in roots:
      n = mod((3 + r) * half, p2)
      if n < min_n:
        min_n = n
    s += min_n

  return s, time() - t

""" Straightforward problem. The problem reduces to finding the sum of the 
    minima of every k-window in a list of numbers. This can be achieved in 
    linear time with a double-ended queue """
def euler_485(N = 10**8, k = 10**5):
    t, s = time(), 0
    num_divs = divisor_num_sieve(N)[1:]
    Q = deque()

    # Consider the first k window i,e, the one that starts at 
    # position 0
    for i in range(k):
        while len(Q) != 0 and num_divs[i] >= num_divs[Q[-1]]:
            Q.pop()
        Q.append(i)

    # Compute the minima of the rest of the windows
    for i in range(k, N):
        s += num_divs[Q[0]]
        while len(Q) != 0 and num_divs[i] >= num_divs[Q[-1]]:
            Q.pop()
        while len(Q) != 0 and Q[0] <= i - k:
            Q.popleft()
        Q.append(i)

    return s + num_divs[Q[0]], time() - t
