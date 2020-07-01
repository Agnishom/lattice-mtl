import re

def has_another_line(file):
    cur_pos = file.tell()
    does_it = bool(file.readline())
    file.seek(cur_pos)
    return does_it

class Results(object):
    def __init__(self):
        self.results = {'Our Tool' : {}, 'Reelay' : {}}
        self.timestamps = []

    def consume_rule(self, fh):
        """parses a horizontal rule. Raises an Assertion Error if this isn't a horizontal rule

        Parameters:
            fh : file handler
        """
        line = fh.readline()
        return (re.compile('\-*').match(line).span() == (0, len(line)-1))

    def getFormulacell(self, tool, formula):
        """finds the corresponding list for the formulae with this tool. this is created if non-existent

        Parameters:
            tool : the tool used
            formula : the formula
        Returns:
            the corresponding list
        """
        if formula not in self.results[tool]:
            self.results[tool][formula] = []
        return self.results[tool][formula]

    def parse_unit(self, fh):
        """parses an unital block

        Parameters:
            fh : file handler
        """
        if not self.consume_rule(fh):
            return
        line = fh.readline()
        tool = re.compile(r"tool = (.*)", re.IGNORECASE).match(line).group(1)
        formula = fh.readline()[:-1]
        line = fh.readline()
        strmlen = int(re.compile(r"stream length = (.*)", re.IGNORECASE).match(line).group(1))
        line = fh.readline()
        duration = float(re.compile(r"duration = (.*) sec", re.IGNORECASE).match(line).group(1))
        line = fh.readline()
        throughput = float(re.compile(r"throughput = (.*) items/sec", re.IGNORECASE).match(line).group(1))
        formcell = self.getFormulacell(tool, formula)
        formcell.append({'strmlen': strmlen, 'duration': duration, 'throughput': throughput})

    def parse_file(self, fh):
        """parses a results file

        Parameters:
            fh : file handler
        """
        line = fh.readline()
        timestamp = float(re.compile(r"timestamp = (.*) seconds after epoch", re.IGNORECASE).match(line).group(1))
        self.timestamps.append(timestamp)
        while has_another_line(fh):
            self.parse_unit(fh)

    def getMean(self, tool, formula):
        return sum(map(lambda x : x['throughput'], self.getFormulacell(tool, formula)))/ len(self.getFormulacell(tool, formula))

    def getDeviation(self, tool, formula):
        mean = self.getMean(tool, formula)
        values = self.getFormulacell(tool, formula)
        length = len(values)
        tmp = sum(map(lambda x : (x['throughput'] - mean) ** 2, values)) / length
        return tmp ** 0.5
