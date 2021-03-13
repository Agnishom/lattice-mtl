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
    return (f//4, f%4)

formulaLabels = ['$P_{[0,n]}$', '$P_{n}$', '$P_{[n,2n]}$', '$P_{[n,\infty)}$',
                 '$S_{[0,n]}$', '$S_{n}$', '$S_{[n,2n]}$', '$S_{[n,\infty)}$']

tool_color = {'Reelay': 'tab:orange', 'semiring-monitor': 'tab:blue', 'lattice-monitor': 'tab:green'}
type_lsty = {'Increasing': '-.', 'Decreasing': ':', 'Random': '-'}

micro_df = pd.read_csv('../logs/micro.log')
micro_df["TimePerItem"] = micro_df["TimeElapsed"]*1000/micro_df["StreamLength"] # (microseconds)
micro_df = micro_df[micro_df['Experiment']=='micro'][['FormulaNumber', 'Bound', 'Tool', 'InputType', 'TimePerItem']]
micro_df = micro_df.groupby(['FormulaNumber', 'Tool', 'Bound', 'InputType'], as_index=False).agg({'TimePerItem' : ['mean', 'std']})

fig, ax = plt.subplots(nrows=2, ncols=4, sharey=True, figsize=(24, 7))
plt.subplots_adjust(hspace=0.3)

lines = dict()


for formula in sorted(micro_df['FormulaNumber'].unique()):
    boxIndex = axIndex(formula)
    ax[boxIndex].set_yscale('log')
    ax[boxIndex].set_xscale('log')
    xticks = sorted(micro_df[micro_df['FormulaNumber'] == formula]['Bound'].unique())
    ax[boxIndex].set_xticks(xticks)
    ax[boxIndex].xaxis.set_ticklabels(toExpLabels(xticks, 4))
    ax[boxIndex].set_title(formulaLabels[int(formula)])
    for tool in tool_color.keys():
        for intype in type_lsty.keys():
            fil = (micro_df['FormulaNumber'] == formula) & (micro_df['Tool'] == tool) & (micro_df['InputType'] == intype)
            x = micro_df[fil]['Bound']
            y = micro_df[fil]['TimePerItem']['mean']
            yerr = micro_df[fil]['TimePerItem']['std']
            ax[boxIndex].errorbar(x, y, yerr=yerr,
                                  linestyle=type_lsty[intype], marker='.', color=tool_color[tool],
                                  label=tool+'-'+intype)

lines = ax[0,0].get_lines()
legend1 = fig.legend(lines[0:len(type_lsty)], type_lsty.keys(), loc='upper left')
legend2 = fig.legend(lines[0:len(tool_color) * len(type_lsty):len(type_lsty)], tool_color.keys(), loc='upper right')
plt.gca().add_artist(legend1)

fig.text(0.05, 0.5, 'time-per-item ($\mu s$)', va='center', rotation='vertical')

plt.savefig('../figures/micro.pdf')
