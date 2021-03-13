# Heaptrack Massif Output

def peek_line(f):
    pos = f.tell()
    line = f.readline()
    f.seek(pos)
    return line

class HeaptrackData(object):

    """
    To use this:
    obj = MassifData('massif.out.8474')

    Useful fields:
        obj.desc
        obj.cmd
        obj.time_unit
        obj.series

    Useful methods:
        obj.times()
        obj.mems()
    """

    def _readHeaders(self):
        descLine = self.fh.readline()
        self.desc = descLine.split(':')[1][1:-1]
        cmdLine = self.fh.readline()
        self.cmd = cmdLine.split(':')[1][1:-1]
        timeLine = self.fh.readline()
        self.time_unit = cmdLine.split(':')[1][1:-1]

    def _body(self):
        while (peek_line(self.fh) != ''):
            self._snapshot()

    def _snapshot(self):
        self.fh.readline()
        self.fh.readline()
        self.fh.readline()
        timeLine = self.fh.readline()
        time = float(timeLine.split('=')[1])
        heapBLine = self.fh.readline()
        heapB = int(heapBLine.split('=')[1])
        heapExtraBLine = self.fh.readline()
        heapExtraB = int(heapExtraBLine.split('=')[1])
        self.fh.readline() #ignoring mem_stacks_B; this is usually turned off
        heapTreeLine = self.fh.readline()
        #print(heapTreeLine)
        heapTreeStatus = heapTreeLine.split('=')[1:][-1].strip()
        if (heapTreeStatus == 'empty'):
            pass
        elif heapTreeStatus == 'detailed':
            self.fh.readline()
            self._ignoreIndentedLines()
        self.series.append((time, heapB + heapExtraB))
        nextLine = peek_line(self.fh)
        if nextLine and nextLine[0] == '#':
            return #another snapshot
        elif nextLine:
            self._readHeaders()


    def _ignoreIndentedLines(self):
        #ignores until it finds the next unindented line
        while True:
            l = peek_line(self.fh)
            if l and (l[0] != ' ' or l[0] != '\t'):
                self.fh.readline()
            else:
                break

    def _ignoreUntilNextSnapshot(self):
        #ignores until it finds the next #
        while True:
            l = peek_line(self.fh)
            if l and l[0] != '#':
                self.fh.readline()
            else:
                break

    def __init__(self, filepath):
        self.fh = open(filepath, 'r')
        self.series = []
        self._body()

    def times(self):
        return list(map(lambda x: x[0], self.series))

    def mems(self):
        return list(map(lambda x: x[1], self.series))
