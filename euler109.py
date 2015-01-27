# Problem 109 - Darts

from time import time

scores, doubles = [], []
dude = 7

def init():
    global scores, doubles

    for i in range(1, 21):
        scores.append(i)
        scores.append(2*i)
        scores.append(3*i)
        doubles.append(2*i)
    
    scores.append(25)
    scores.append(50)
    doubles.append(50)

    scores = sorted(scores)
    doubles = sorted(doubles)

def count_two_misses():
    global doubles
    return len(doubles)

def count_one_miss():
    global scores, doubles
    count, l = 0, len(scores)
    scores, doubles = scores, doubles

    for i in range(l):
        score = scores[i]
        for d in doubles:
            if score + d >= 100:
                break
            count += 1

    return count

def count_no_misses():
    global scores, doubles
    count, l = 0, len(scores)
    scores, doubles = scores, doubles
    
    for i in range(l):
        first_score = scores[i]
        for j in range(i, l):
            second_score = scores[j] + first_score
            for d in doubles:
                if second_score + d >= 100:
                    break
                count += 1

    return count

def euler_109():
    t = time()    
    init()
    count = count_two_misses() + count_one_miss() + \
            count_no_misses()
    print "Answer:", count
    print "Time:", time() - t

if __name__ == "__main__":
    euler_109()
