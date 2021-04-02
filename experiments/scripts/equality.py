import random
import subprocess
import signal
from math import isclose

tools = { 'lattice-mtl': lambda formula, bound: ["../tools/lattice-mtl/lattice-equality.bin", '-f', str(formula), '-b', str(int(bound))]
        , 'reelay': lambda formula, bound: ["../tools/reelay/reelay-equality.bin", str(formula), str(int(bound))]
        , 'semiring-monitor': lambda formula, bound: ["../tools/semiring-monitor/semiring-equality.bin", str(formula), str(int(bound))]
        }

oracle = 'lattice-mtl'

def random_s(seed = 0, bound = 1):
    random.seed(a = seed)
    while True:
        yield random.uniform(-bound, bound)

def increasing_s(step = 1):
    x = 0
    while True:
        yield x
        x += step

def decreasing_s(step = 1):
    for y in increasing_s(step = -step):
        yield y

def increasing_random_s(seed = 0, l = 0, u = 1):
    assert l < u
    random.seed(a = seed)
    x = 0
    while True:
        yield x
        x += random.uniform(l, u)

def decreasing_random_s(seed = 0, l = 0, u = 1):
    for y in increasing_random_s(seed = 0, l = 0, u = 1):
        yield -y

def runTool(tool, formula, bound, streamfac, strmlen):
    cmd1 = tools[tool](formula, bound)
    p1 = subprocess.Popen(cmd1, stdin=subprocess.PIPE, stderr=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    history = []
    for (_, inp) in zip(range(strmlen), streamfac()):
        p1.stdin.write(str(inp) + '\n')
        history.append(inp)
    stdout, stderr = p1.communicate("DONE")
    return stdout.splitlines(), history

def checkEquality(tool, formula, bound, streamfac, strmlen):
    oracleResult, history = runTool(oracle, formula, bound, streamfac, strmlen)
    oracleResult = list(map(float, oracleResult))
    toolResult, _ = runTool(tool, formula, bound, streamfac, strmlen)
    # dropping extra output terms because this is not always available
    toolResult = list(map(float, toolResult[:strmlen]))
    try:
        assert all((isclose(x, y, rel_tol=0.0001) for x, y in zip(oracleResult, toolResult)))
        return True
    except AssertionError:
        lowest = next (i for (i, (j, k)) in enumerate(zip(oracleResult, toolResult)) if not isclose(j, k, rel_tol=0.0001))
        print("Running " + str(tool) + " on Formula " + str(formula) + " with bound " + str(bound) + " for length " + str(strmlen))
        print("Input History: ", history[:lowest+2*bound+1])
        print("Oracle Output:", oracleResult[:lowest+1])
        print("Tool Output:", toolResult[:lowest+1])
        return False

nFormula = 8
nBounds = 4
streamfacs = [increasing_s, decreasing_s, random_s, increasing_random_s, decreasing_random_s]


for fff in range(nFormula):
    for tool in tools:
        for streamfac in streamfacs:
            bound = 1
            for _ in range(nBounds):
                if not checkEquality(tool, fff, bound, streamfac, bound*4+5):
                    break
                bound *= 2
            else:
                continue
            break
