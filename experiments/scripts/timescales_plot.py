import pandas as pd
import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt
import math

def toExpLabels(ticks, sparsity=1):
    f = lambda pair: ('' if pair[0]%sparsity else '$2^{' + str(int(math.log2(pair[1]))) + '}$')
    ticklabels = map(f, enumerate(ticks))
    return list(ticklabels)

def axIndex(formula):
    f = int(formula)
    return (f//5, f%5)

#############################
# timescales benchmarks
#############################

formulaLabels = ["$F_"+str(i)+ "(n)$" for i in range(10)]

tool_color = {'Reelay': 'tab:orange', 'semiring-monitor': 'tab:blue', 'lattice-monitor': 'tab:green'}
type_lsty = {'Increasing': '-.', 'Decreasing': ':', 'Random': '-'}

timescales_df = pd.read_csv('../logs/timescales.log')
timescales_df["TimePerItem"] = timescales_df["TimeElapsed"]*1000/timescales_df["StreamLength"] # (microseconds)
timescales_df = timescales_df[timescales_df['Experiment']=='timescales'][['FormulaNumber', 'Bound', 'Tool', 'TimePerItem']]
timescales_df = timescales_df.groupby(['FormulaNumber', 'Tool', 'Bound'], as_index=False).agg({'TimePerItem' : ['mean', 'std']})

fig, ax = plt.subplots(nrows=2, ncols=5, sharey=True, figsize=(24, 7))
plt.subplots_adjust(hspace=0.3)

lines = dict()

for formula in sorted(timescales_df['FormulaNumber'].unique()):
    boxIndex = axIndex(formula)
    ax[boxIndex].set_yscale('log')
    ax[boxIndex].set_xscale('log')
    ax[boxIndex].tick_params(axis='both', which='major', labelsize=24)
    xticks = sorted(timescales_df[timescales_df['FormulaNumber'] == formula]['Bound'].unique())
    if boxIndex[0] == 1:
        ax[boxIndex].set_xticks(xticks)
        ax[boxIndex].xaxis.set_ticklabels(toExpLabels(xticks, 4), fontsize=26)
    else:
        ax[boxIndex].set_xticks(xticks)
        ax[boxIndex].xaxis.set_ticklabels('')
    ax[boxIndex].set_title(formulaLabels[int(formula)], fontsize=30)
    for tool in tool_color.keys():
            fil = (timescales_df['FormulaNumber'] == formula) & (timescales_df['Tool'] == tool)
            x = timescales_df[fil]['Bound']
            y = timescales_df[fil]['TimePerItem']['mean']
            yerr = timescales_df[fil]['TimePerItem']['std']
            ax[boxIndex].errorbar(x, y, yerr=yerr,
                                  linestyle='-', marker='.', color=tool_color[tool],
                                  label=tool)

plt.legend(fontsize=24, bbox_to_anchor=(-4,2.60), loc="lower left", borderaxespad=0, ncol=5)

fig.text(0.05, 0.5, 'time-per-item ($\mu s$)', va='center', rotation='vertical', fontsize=26)

plt.savefig('../figures/timescales.pdf', bbox_inches='tight', pad_inches=0.5)
