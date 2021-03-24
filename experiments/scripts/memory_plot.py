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

memory_df = pd.read_csv('../logs/memory.2.log')
memory_df = memory_df[memory_df['Experiment']=='memory'][['FormulaNumber', 'Bound', 'Tool', 'InputType', 'Memory']]
memory_df['Memory'] = memory_df['Memory']/1000.0
#memory_df = memory_df[memory_df['Bound'] >= 2**9]
memory_df = memory_df.groupby(['FormulaNumber', 'Tool', 'Bound', 'InputType'], as_index=False).agg({'Memory' : ['mean', 'std']}).dropna()


fig, ax = plt.subplots(nrows=2, ncols=4, sharey=True, figsize=(24, 7))
plt.subplots_adjust(hspace=0.3)
#plt.subplots_adjust(wspace=0.1)

lines = dict()

for formula in sorted(memory_df['FormulaNumber'].unique()):
    boxIndex = axIndex(formula)
    ax[boxIndex].set_yscale('log')
    ax[boxIndex].set_xscale('log')
    ax[boxIndex].tick_params(axis='both', which='major', labelsize=24)
    xticks = sorted(memory_df[memory_df['FormulaNumber'] == formula]['Bound'].unique())
    if boxIndex[0] == 1:
        ax[boxIndex].set_xticks(xticks)
        ax[boxIndex].xaxis.set_ticklabels(toExpLabels(xticks, 4), fontsize=26)
    else:
        ax[boxIndex].set_xticks(xticks)
        ax[boxIndex].xaxis.set_ticklabels('')
    ax[boxIndex].set_title(formulaLabels[int(formula)], fontsize=30)
    for tool in tool_color.keys():
        for intype in type_lsty.keys():
            if (intype != 'Random' and tool != 'Reelay'):
                continue
            fil = (memory_df['FormulaNumber'] == formula) & (memory_df['Tool'] == tool) & (memory_df['InputType'] == intype)
            x = memory_df[fil]['Bound']
            y = memory_df[fil]['Memory']['mean']
            yerr = memory_df[fil]['Memory']['std']
            ax[boxIndex].errorbar(x, y,
                                  linestyle=type_lsty[intype], marker='.', color=tool_color[tool],
                                  label=tool+('-'+intype if tool == 'Reelay' else ''))

# lines = ax[0,0].get_lines()
# legend1 = fig.legend(lines[0:len(type_lsty)], type_lsty.keys(), loc='upper left')
# legend2 = fig.legend(lines[0:len(tool_color) * len(type_lsty):len(type_lsty)], tool_color.keys(), loc='upper right')
# plt.gca().add_artist(legend1)
plt.legend(fontsize=24, bbox_to_anchor=(-4,2.60), loc="lower left", borderaxespad=0, ncol=5)

fig.text(0.05, 0.5, 'memory (KB)', va='center', rotation='vertical', fontsize=26)
#fig.tight_layout()

plt.savefig('../figures/memory.2.pdf', bbox_inches='tight', pad_inches=0)
