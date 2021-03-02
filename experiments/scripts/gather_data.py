import os
import pandas as pd

raw_path = '../logs/raw/'
ripe_path = '../logs/'

# given a file, extract data from it
def getDataFromRawFile(filename):
    f = open(raw_path + filename,'r')
    datum = dict()
    for line in f.readlines():
        chunks = line.split('=')
        if len(chunks) != 2:
            continue
        if chunks[0] in ['Bound', 'StreamLength', 'TimeElapsed', 'FormulaNumber', 'Memory']:
            datum[chunks[0]] = float(chunks[1].strip())
        elif chunks[0] in ['Experiment', 'Tool', 'Formula', 'TimeUnit']:
            datum[chunks[0]] = chunks[1].strip()
    return datum

def getRawData():
    filenames = os.listdir(raw_path)
    data = []
    for filename in filenames:
        datum = getDataFromRawFile(filename)
        datum['TimeStamp'] = pd.to_datetime(filename.split('.')[0])
        data.append(datum)
    return pd.DataFrame(data)

def cleanupRawData():
    data = getRawData()
    data.to_csv(ripe_path + str(max(data['TimeStamp'])) + '.log', index=False)
