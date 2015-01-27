from time import time

""" This is relatively straightforward DP """
def euler_208(n = 25, k = 5):
    t = time()
    cache = {}
    
    r = n/k + 1
    s = [n/k] * k

    def count_paths(s):
        if any(x < 0 for x in s):
            return 0
        elif all(x == 0 for x in s):
            return 1

        key = 0
        # Evaluate a polynomial with Horner's scheme
        for x in s:
            key = (key * r) + x

        if key in cache:
            return cache[key]
        else:
            s1 = s[1:] + [s[0] - 1]
            num_paths = count_paths(s1)

            s2 = [s[-1] - 1] + s[:-1]
            num_paths += count_paths(s2)
            
            cache[key] = num_paths
            return num_paths

    return count_paths(s), time() - t
            

print euler_208()
