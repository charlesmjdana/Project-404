# **************************************************************************** #
#                                                                              #
#                                                         :::      ::::::::    #
#    fast.py                                            :+:      :+:    :+:    #
#                                                     +:+ +:+         +:+      #
#    By: charles <charles.dana@hec.edu>             +#+  +:+       +#+         #
#                                                 +#+#+#+#+#+   +#+            #
#    Created: 2023/04/09 19:46:15 by charles           #+#    #+#              #
#    Updated: 2023/04/09 23:41:32 by charles          ###   ########.fr        #
#                                                                              #
# **************************************************************************** #

"""
This is a python prototype, who's purpose is to demonstrate the interest in the use of
    real functions with n boolean variables to improve knowledge about a SAT Instance
    It will always output a SAT Instance, with a decreasing number of clause of length > 2
    It is hard to find instance where it doesn't perform
    But at some point it struggles at generating new ones

If you wish to know more about this python script genesis, please contact: charles.dana@hec.edu
"""


def convert(clause):
    f = {0 : -0.5}
    for x in clause:
        if x > 0:
            f[x] = 1.0
        if x < 0:
            f[-x] = -1.0
            f[0] += 1.0
    return f

def add(f, g):
    h = {0 : 0}
    for x in f:
        if not x in h:
            h[x] = 0
        h[x] += f[x]
    for x in g:
        if not x in h:
            h[x] = 0
        h[x] += g[x]
    return h

def scalar(f, lbd):
    g = {0 : 0}
    for x in f:
        g[x] = f[x] * lbd
    return g

def norm(f):
    nrm = 0
    for x in f:
        nrm += f[x] ** 2
    return nrm ** 0.5

def fit(f):
    score = f[0]
    keyval = sorted([[x, f[x]] for x in f if x > 0], key=lambda X: -abs(X[1]))
    for x in f:
        if x > 0:
            score += 0.5 * (f[x] + abs(f[x]))
    return score - sum((abs(keyval[t][1]) for t in range(min(3, len(keyval)))))

def evaluate(f, solution):
    score = f[0]
    keyval = sorted([[x, f[x]] for x in f if x > 0 and solution[x] == "?"], key=lambda X: -abs(X[1]))
    for x in f:
        if x > 0:
            if solution[x] == "?":
                score += 0.5 * (f[x] + abs(f[x]))
            if solution[x] == "1":
                score += f[x]
    if score < -0.1:
        return []
    if score - sum((abs(keyval[t][1]) for t in range(min(1, len(keyval))))) < 0:
        x = keyval[0][0]
        if f[x] > 0:
            return [x] # Add to the contribution
        if f[x] < 0:
            return [-x] # Do not add to the contribution
    if score - sum((abs(keyval[t][1]) for t in range(min(2, len(keyval))))) < 0:
        x = keyval[0][0]
        y = keyval[1][0]
        clause = []
        for a in [x, y]:
            if f[a] > 0:
                clause += [a]
            else:
                clause += [-a]
        return clause
    if score - sum((abs(keyval[t][1]) for t in range(min(3, len(keyval))))) < 0:
        x = keyval[0][0]
        y = keyval[1][0]
        z = keyval[2][0]
        clause = []
        for a in [x, y, z]:
            if f[a] > 0:
                clause += [a]
            else:
                clause += [-a]
        return clause
    return 0


"""
PARSER SECTION:
    Capable of parsing most if not any dimac file I have encountered
    For documentation see: https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/satformat.ps
"""

def check(line):
    if len(line) == 0:
        return False
    i = 0 
    while (i < len(line)):
        j = 0 
        if line[i] == 0:
            return False
        while (j < i): 
            if abs(line[i]) == abs(line[j]):
                return False
            j = j + 1 
        i = i + 1 
    return True

def read(fname):
    problem = list()
    if not ".cnf" in fname:
        print("Error, not a .cnf file")
    i = 0 
    with open(fname, 'r') as f:
        for line in f.read().splitlines():
            if len(line) > 0 and not line[0] in "%cp":
                lst = []
                for x in line.split(" "):
                    if x != '' and not int(x) == 0:
                        lst.append(int(x))
                if check(lst):
                    problem += [lst]
                    i = i + 1 
    return (problem)

from random import choice, randint

def torun(problem, solution):
    for clause in problem:
        test = False
        for x in clause:
            if x > 0 and solution[x] == "1":
                test = True
            if x < 0 and solution[-x] == "0":
                test = True
        if not test:
            return True
    return False

from time import time

def improve(problem, duration=1):
    t_0 = time()
    F = [convert(clause) for clause in problem]
    while time() - t_0 < duration:
        f = choice(F)
        g = choice(F)
        nf = norm(f)
        ng = norm(g)
        if nf * ng > 0:
            h = add(f, g)
            if norm(h) == 0:
                best = fit(h)
            else:
                best = fit(h) / norm(h)
            for dummy_trial in range(100):
                lbdf = randint(1, 10) / nf
                lbdg = randint(1, 10) / ng
                crt = add(scalar(f, lbdf), scalar(g, lbdg))
                if fit(crt) / norm(crt) < best:
                    best = fit(crt) / norm(crt)
                    h = crt
            if best < -0.1:
                F += [h]
                associated_clause = evaluate(h, {abs(x) : "?" for clause in problem for x in clause})
                if associated_clause != 0 and not associated_clause in problem:
                    problem += [associated_clause]
                    F += [convert(associated_clause)]
    return problem

def dig(problem, duration=1):
    unit = []
    if [] in problem:
        return "UNSAT"
    t_0 = time()
    while time() - t_0 < duration:
        preprocessed = sorted(list(set([tuple(sorted(clause)) for clause in problem])), key=lambda X: len(X))
        problem = [list(clause) for clause in preprocessed]
        x = 0
        z = 0
        for clause in problem:
            if len(clause) == 1:
                x = clause[0]
                break
            if len(clause) == 2:
                a = clause[0]
                b = clause[1]
                if [a, -b] in problem or [-b, a] in problem:
                    z = a
                if [b, -a] in problem or [-a, b] in problem:
                    z = b
        if x == 0 and z == 0:
            break
        if z != 0:
            problem += [[z]]
        elif x != 0:
            unit += [x]
            """
            DEBUG MODE
            for clause in problem:
                if x in clause:
                    print("Implication of " + str(x) + ": " + str(clause))
            """
            problem = [clause for clause in problem if not x in clause] # Right to forget the ones containing x
            problem = [[y for y in clause if not -y == x] for clause in problem] # Removal of mensions of -x
    return problem + [[x] for x in unit]


import sys

if __name__ == "__main__":
    if len(sys.argv) == 1:
        print("Usage: python problem.cnf")
        exit()
    problem = read(sys.argv[1])
    initial = [[x for x in clause] for clause in problem]
    print("7 seconds of search, then boolean constraint propagation (at most 60s):")
    problem = improve(problem, 7)
    problem = dig(problem, 42)
    print("Equivalent SAT Instance:")
    result = dig(initial + [clause for clause in problem if len(clause) < 3], 7)
    result = sorted(result, key=lambda clause: -len(clause))
    for clause in result:
        print(" ".join([str(x) for x in clause]) + " 0")

