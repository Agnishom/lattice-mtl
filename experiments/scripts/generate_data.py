import os.path
import subprocess

tools = { 'lattice-mtl': { 'micro': lambda formula, strmlen, bound: ["../tools/lattice-mtl/lattice-micro.bin", '-f', str(formula), '-l', str(int(strmlen)), '-b', str(int(bound))]
                         , 'timescales' : lambda formula, strmlen, bound: ["../tools/lattice-mtl/lattice-timescales.bin", '-f', str(formula), '-l', str(int(strmlen)), '-b', str(int(bound))] }
        , 'reelay': { 'micro': lambda formula, strmlen, bound: ["../tools/reelay/reelay-micro.bin", str(formula), str(int(strmlen)), str(int(bound))]
                    , 'timescales': lambda formula, strmlen, bound: ["../tools/reelay/reelay-timescales.bin", str(formula), str(int(strmlen)), str(int(bound))] }
        , 'semiring-monitor': { 'micro': lambda formula, strmlen, bound: ["../tools/semiring-monitor/semiring-micro.bin", str(formula), str(int(strmlen)), str(int(bound))]
                              , 'timescales': lambda formula, strmlen, bound: ["../tools/semiring-monitor/semiring-timescales.bin", str(formula), str(int(strmlen)), str(int(bound))] }}

def checkBinaryExists():
    for tool in tools:
        for bin in tools[tool]:
            if not os.path.exists(bin):
                raise AssertionError(bin + " does not exist")

def runExperiment(expname, tool, formula, strmlen, bound):
    timenow = subprocess.run(['date', '-Ins'], capture_output=True).stdout
    f = open('../logs/raw/'+timenow.decode('utf-8')[:-1]+'.log', 'xb')
    f.write(bytes('Experiment='+ expname +'\n', 'utf-8'))
    f.write(bytes('FormulaNumber='+str(formula)+'\n', 'utf-8'))
    f.write(bytes('Bound='+str(bound)+'\n', 'utf-8'))
    p = subprocess.run(tools[tool][expname](formula, strmlen, bound), capture_output=True)
    f.write(p.stdout)
    f.close()

def strmlen(expname, tool, formula, bound):
    if expname == 'micro':
        if tool == 'semiring-monitor':
            return 300000000 # 300 million
        elif tool == 'lattice-mtl':
            return 10000000 # 10 million
        elif tool == 'reelay':
            if formula in [1, 5]:
                return (500000 if bound < 8000 else bound*4)
            else:
                return 5000000 # 5 million
    elif expname == 'timescales':
        if tool == 'semiring-monitor':
            return 100000000 # 100 million
        elif tool == 'lattice-mtl':
            return 5000000 # 5 million
        elif tool == 'reelay':
            return 5000000 # 5 million

nMICROFORMULA = 8
nTIMESCALEFORMULA = 10
uB = 20
nTRIALS = 10

def runMicro1(uB = uB):
    for _ in range(nTRIALS):
        for bbb in range(4, uB):
            for fff in range(nMICROFORMULA):
                for tool in tools:
                    if not (tool == 'reelay' and (fff == 1 or fff == 5)):
                        bound = 2 ** bbb
                        runExperiment('micro', tool, fff, strmlen('micro', tool, fff, bound), bound)

def runMicro2(uB = 16):
    for _ in range(nTRIALS):
        for bbb in range(4, uB):
            for fff in range(nMICROFORMULA):
                for tool in tools:
                    if (tool == 'reelay' and (fff == 1 or fff == 5)):
                        bound = 2 ** bbb
                        runExperiment('micro', tool, fff, strmlen('micro', tool, fff, bound), bound)

def runTimescales(uB = uB):
    for _ in range(nTRIALS):
        for bbb in range(4, uB):
            for fff in range(nTIMESCALEFORMULA):
                for tool in tools:
                    bound = 2 ** bbb
                    runExperiment('timescales', tool, fff, strmlen('timescales', tool, fff, bound), bound)

#runMicro1()
#runMicro2()
runTimescales()
