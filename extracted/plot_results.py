from parse_results import Results

import numpy as np
import matplotlib
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

matplotlib.use('Agg')

results = Results()
results.parse_file(open('reelay_results', 'r'))
results.parse_file(open('ourtool_results', 'r'))

# The stacked comparison of formulae

formulae = ["{x > 0.5}", "{x > 0.25}", "{x > 0.5} and {x > 0.25}", "{x > 0.5} or {x > 0.25}",
            "once {x > 0.5}", "historically {x > 0.5}", "{x > 0.5} since {x > 0.25}",
            "once [10:10] {x > 0.5}", "{x > 0.5} since[1000:2000] {x > 0.25}", "once[:1000] {x > 0.5}"]

ourtool_means = np.array(list(map(lambda f : results.getMean('Our Tool', f), formulae)))
reelay_means = np.array(list(map(lambda f : results.getMean('Reelay', f), formulae)))

ourtool_std = np.array(list(map(lambda f : results.getDeviation('Our Tool', f), formulae)))
reelay_std = np.array(list(map(lambda f : results.getDeviation('Reelay', f), formulae)))

xlocs = np.arange(len(formulae))
width = 0.3

fig, ax = plt.subplots(figsize=(6.4,4.8))
rects1 = ax.bar(xlocs - width/2, ourtool_means, 0.9*width, yerr=ourtool_std, label='Our Tool')
rects2 = ax.bar(xlocs + width/2, reelay_means, 0.9*width, yerr=reelay_std, label='Reelay')

# Add some text for labels, title and custom x-axis tick labels, etc.
plt.yscale('log')
scale_y = 1e4
ticks_y = ticker.FuncFormatter(lambda x, pos: '{0:g}'.format(x/scale_y))
ax.yaxis.set_major_formatter(ticks_y)

ax.set_ylabel('throughput (10k items/sec)')
ax.set_xticks(xlocs)
#ax.set_xticklabels(formulae, rotation=70)
ax.set_xticklabels(["F"+str(i) for i in range(len(formulae))])
plt.xticks(fontsize=9)
ax.legend(fontsize=8)

fig.tight_layout()

plt.show()
plt.savefig("general.pdf", papertype=None, format=None,
        transparent=False, bbox_inches=None, pad_inches=0.1,
        facecolor=None, metadata=None)

# The line graphs showing how the operators scale

formschemes = ["Our Tool (P_k)", "Our Tool (P_[0,k])", "Our Tool (Since_[0,k])", "Reelay (P_k)", "Reelay (P_[0,k])", "Reelay (Since_[0,k])"]
kvalues = [10, 100, 1000, 10000, 100000]
ourtoolpkmeans = np.array(list(map(lambda k : results.getMean('Our Tool', 'once [' + str(k) + ':' + str(k) + '] {x > 0.5}')  , kvalues)))
ourtoolpOkmeans = np.array(list(map(lambda k : results.getMean('Our Tool', 'once[:' + str(k) + '] {x > 0.5}')  , kvalues)))
ourtoolsinceOkmeans = np.array(list(map(lambda k : results.getMean('Our Tool', '{x > 0.5} since[:'+ str(k) +'] {x > 0.25}')  , kvalues)))
reelaypkmeans = np.array(list(map(lambda k : results.getMean('Reelay', 'once [' + str(k) + ':' + str(k) + '] {x > 0.5}')  , kvalues)))
reelaypOkmeans = np.array(list(map(lambda k : results.getMean('Reelay', 'once[:' + str(k) + '] {x > 0.5}')  , kvalues)))
reelaysinceOkmeans = np.array(list(map(lambda k : results.getMean('Reelay', '{x > 0.5} since[:'+ str(k) +'] {x > 0.25}')  , kvalues)))

import matplotlib.pyplot as plt

fig, ax = plt.subplots(figsize=(6.4,4.8))
xlocs = np.arange(len(formschemes))

ax.plot(kvalues, ourtoolpkmeans, label = "Our Tool (P_k)")
ax.plot(kvalues, ourtoolpOkmeans, label = "Our Tool (P_[0,k])")
ax.plot(kvalues, ourtoolsinceOkmeans, label = "Our Tool (Since_[0,k])")
ax.plot(kvalues, reelaypkmeans, label = "Reelay (P_k)")
ax.plot(kvalues, reelaypOkmeans, label = "Reelay (P_[0,k])")
ax.plot(kvalues, reelaysinceOkmeans, label = "Reelay (Since_[0,k])")

# Add some text for labels, title and custom x-axis tick labels, etc.
plt.yscale('log')
scale_y = 1e4
ticks_y = ticker.FuncFormatter(lambda x, pos: '{0:g}'.format(x/scale_y))
ax.yaxis.set_major_formatter(ticks_y)
ax.set_ylabel('throughput (10k items/sec)')

plt.xscale('log')
ax.set_xticks(kvalues)
# scale_x = 10
# ticks_x = ticker.FuncFormatter(lambda x, pos: '{0:g}'.format(x/scale_x))
# ax.yaxis.set_major_formatter(ticks_x)

plt.legend(loc='lower left')

fig.tight_layout()

plt.show()
plt.savefig("scale.pdf", papertype=None, format=None,
        transparent=False, bbox_inches=None, pad_inches=0.1,
        facecolor=None, metadata=None)
