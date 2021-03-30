import random
import subprocess
import signal

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

def runTool(tool, formula, bound, stream, strmlen):
    timenow = subprocess.run(['date', '-Ins'], capture_output=True).stdout
    filename = '../logs/raw/'+timenow.decode('utf-8')[:-1]+'.log'
    cmd1 = tools[tool](formula, bound)
    f = open(filename, 'w')
    p1 = subprocess.Popen(cmd1, shell=True, stdin=subprocess.PIPE, stderr=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    for (_, inp) in zip(range(strmlen), stream):
        p1.stdin.write(str(inp) + '\n')
        #p1.stdin.flush()
    p1.stdin.flush()
    print(p1.stdout.readline())
    p1.kill()
    f.close()

runTool('lattice-mtl', 1, 10, increasing_s(), 10)
