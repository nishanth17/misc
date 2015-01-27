# Problem 226 - A Scoop of Blancmange
# Answer: 0.1136017
# Time: 0.12s (w/ PyPy)

import math
from time import time

# Note: This works only when 0 <= x <= 1
def s(x):
    return 1 - x if x > 0.5 else x

# Note: The fractional part converges to 0.5 for
# every damn number due to floating point rounding
# errors. This means any that cycle (0.2 -> 0.4 -> 0.8
# -> 0.6 -> 0.2 for example) will also converge to 0.5.
def blancmange(x, eps = 1e-9):
    x, pow2 = float(x), 1

    b = 0
    while x > eps:
        b += s(x) / pow2
        x *= 2
        pow2 <<= 1
        
        # Note that it suffices to work with the fractional
        # part of a number since we are concerned with its
        # distance to the closest integer which is <= 1/2.
        x = x - int(x)

    return b

# (x - 1/4)^2 + (y - 1/2)^2 = 1/16    
def circle(x):
    return (1 - math.sqrt(2*x * (1 - 2*x))) / 2

# Inverse quadratic interpolation - this converges about twice
# as fast as the bisection method
def iqe(lo, hi, eps = 1e-16, f = diff):
    x0, x1, x2 = hi, lo, (lo + hi) / 2
    f0, f1, f2 = f(x0), f(x1), f(x2)

    while f0 != f1 and f1 != f2 and f0 != f2:
        x3 = f1*f2*x0/((f0-f1)*(f0-f2)) + f0*f2*x1/((f1-f2)*(f1-f0)) \
             + f0*f1*x2/((f2-f1)*(f2-f0))

        f3 = f(x3)
        if abs(f3) < eps:
            return x3
        
        x2, x1, x0 = x3, x2, x1
        f2, f1, f0 = f3, f2, f1

    return x2

# Numerical integration with the trapezoidal rule i.e. this
# approximates integral(f(x)dx, x = a to b) with n intervals
def numerical_integral(f, a, b, n):
    d = (b - a) / n
    integral, x = 0, a

    for k in range(n - 1):
        x += d
        integral += f(x)

    integral = d * (f(a)/2 + integral + f(b)/2)
    return integral

# Runs the program
if __name__ == "__main__":
    t = time()
    a, b = iqe(0, 0.25), 0.5
    num_intervals = 10**5

    area = numerical_integral(lambda x : blancmange(x) - circle(x), \
                              a, b, num_intervals)
    print "Answer:", round(area, 8)
    print "Time:", time() - t
