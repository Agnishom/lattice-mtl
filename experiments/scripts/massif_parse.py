def peek_line(f):
    pos = f.tell()
    line = f.readline()
    f.seek(pos)
    return line

class MassifData(object):

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

    def _initblock(self):
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
        time = int(timeLine.split('=')[1])
        heapBLine = self.fh.readline()
        heapB = int(heapBLine.split('=')[1])
        heapExtraBLine = self.fh.readline()
        heapExtraB = int(heapExtraBLine.split('=')[1])
        self.fh.readline() #ignoring mem_stacks_B; this is usually turned off
        self._ignoreUntilNextSnapshot()
        self.series.append((time, heapB + heapExtraB))

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
        self._initblock()
        self.series = []
        self._body()

    def times(self):
        return list(map(lambda x: x[0], self.series))

    def mems(self):
        return list(map(lambda x: x[1], self.series))
