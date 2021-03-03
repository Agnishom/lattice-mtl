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
# micro benchmarks
#############################

formulaLabels = ['$P_{[0,n]}$', '$P_{n}$', '$P_{[n,2n]}$', '$P_{[n,\infty)}$',
                 '$S_{[0,n]}$', '$S_{n}$', '$S_{[n,2n]}$', '$S_{[n,\infty)}$']

micro_df = pd.read_csv('../logs/micro.log')
micro_df["TimePerItem"] = micro_df["TimeElapsed"]*1000/micro_df["StreamLength"] # (microseconds)
micro_df = micro_df[micro_df['Experiment']=='micro'][['FormulaNumber', 'Bound', 'Tool', 'TimePerItem']]
#micro_df = micro_df.groupby(['FormulaNumber', 'Tool', 'Bound'], as_index=False).agg({'TimePerItem' : ['mean', 'std']})

g = sns.FacetGrid(micro_df, col="FormulaNumber", col_wrap = 4, height=2, hue='Tool')
g.map(sns.lineplot, "Bound", "TimePerItem", err_style='bars').set(yscale='log', xscale='log')
xticks = sorted(micro_df['Bound'].unique())
g.set(xticks=xticks, xticklabels = toExpLabels(xticks, 4))
g.set_ylabels('')
g.set_xlabels('')
g.fig.text(0.02, 0.5, 'time-per-item ($\mu s$)', va='center', rotation='vertical')
for (i, ax) in enumerate(g.axes):
    ax.set_title(formulaLabels[i])
g.add_legend(loc='lower center', bbox_to_anchor=(0.4,1), ncol=4, title=None)
g.savefig('../figures/micro.pdf')

#############################
# memory benchmarks
#############################

formulaLabels = ['$P_{[0,n]}$', '$P_{n}$', '$P_{[n,2n]}$', '$P_{[n,\infty)}$',
                 '$S_{[0,n]}$', '$S_{n}$', '$S_{[n,2n]}$', '$S_{[n,\infty)}$']

memory_df = pd.read_csv('../logs/memory.log')
memory_df = memory_df[memory_df['Experiment']=='memory'][['FormulaNumber', 'Bound', 'Tool', 'Memory']]
memory_df['Memory'] = memory_df['Memory']/1000.0

g = sns.FacetGrid(memory_df, col="FormulaNumber", col_wrap = 4, height=2, hue='Tool')
g.map(sns.lineplot, "Bound", "Memory", err_style='bars').set(yscale='log', xscale='log')
xticks = sorted(memory_df['Bound'].unique())
g.set(xticks=xticks, xticklabels = toExpLabels(xticks, 4))
g.set_ylabels('')
g.set_xlabels('')
g.fig.text(0.02, 0.5, 'Peak Memory Usage (KB)', va='center', rotation='vertical')
for (i, ax) in enumerate(g.axes):
    ax.set_title(formulaLabels[i])
g.add_legend(loc='lower center', bbox_to_anchor=(0.4,1), ncol=4, title=None)
g.savefig('../figures/memory.pdf')

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
