import pandas as pd
import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt
import math

def toExpLabels(ticks, sparsity=1):
    f = lambda pair: ('' if pair[0]%sparsity else '$2^{' + str(int(math.log2(pair[1]))) + '}$')
    ticklabels = map(f, enumerate(ticks))
    return list(ticklabels)

#############################
# timescales benchmarks
#############################

formulaLabels = ["F"+str(i)+ "(n)" for i in range(10)]

timescales_df = pd.read_csv('../logs/timescales.log')
timescales_df["TimePerItem"] = timescales_df["TimeElapsed"]*1000/timescales_df["StreamLength"] # (microseconds)
timescales_df = timescales_df[timescales_df['Experiment']=='timescales'][['FormulaNumber', 'Bound', 'Tool', 'TimePerItem']]

g = sns.FacetGrid(timescales_df, col="FormulaNumber", col_wrap = 5, height=2, hue='Tool')
g.map(sns.lineplot, "Bound", "TimePerItem", err_style='bars').set(yscale='log', xscale='log')
xticks = sorted(timescales_df['Bound'].unique())
g.set(xticks=xticks, xticklabels = toExpLabels(xticks, 4))
g.set_ylabels('')
g.set_xlabels('')
g.fig.text(0.02, 0.5, 'time-per-item ($\mu s$)', va='center', rotation='vertical')
for (i, ax) in enumerate(g.axes):
    ax.set_title(formulaLabels[i])
g.add_legend(loc='lower center', bbox_to_anchor=(0.4,1), ncol=4, title=None)
g.savefig('../figures/timescales.pdf')
