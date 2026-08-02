"""Regenerate fig_minR_hist.pdf (Figure 1 of the paper).

Log-scale histogram of the minimal-residual distribution over all
128,671,219 hard primes below 10^11, from the distribution of
Table 3 (data/hard_primes_1e11_minimalR.*). The figure is built at
its final printed size (6.3 in = the paper's text width, included at
width=\\linewidth), so font sizes below are true on-page sizes, and
fonts are embedded as vector outlines (pdf.fonttype 42), matching the
paper's Latin Modern text.

Requires matplotlib (pip install -e ".[fig]").

Usage:  python make_fig.py   (from paper/)
"""

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.serif": ["cmr10", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "axes.formatter.use_mathtext": True,
        "axes.unicode_minus": False,
        "font.size": 10,
        "pdf.fonttype": 42,
    }
)

# Table 3 of the paper (10^11 data).
DIST = {
    3: 69951190, 7: 31335473, 11: 19439771, 15: 3974286, 19: 2441687,
    23: 1070808, 27: 187963, 31: 193848, 35: 30784, 39: 25258,
    43: 6850, 47: 8811, 51: 1450, 55: 1369, 59: 954, 63: 283,
    67: 104, 71: 209, 75: 29, 79: 50, 83: 23, 87: 8, 91: 3,
    95: 5, 99: 1, 103: 1, 107: 1,
}

fig, ax = plt.subplots(figsize=(6.3, 3.4))
xs = list(DIST.keys())
ys = [DIST[r] for r in xs]
# The band 87-103 was empty below 10^10 (Section 6.1 of the paper).
ax.axvspan(85, 105, color="0.88", zorder=0)
ax.text(95, 6e6, "band empty\nbelow $10^{10}$", ha="center",
        fontsize=8, color="0.35")
ax.bar(xs, ys, width=3.0, color="#3b5b92", edgecolor="black",
       linewidth=0.4, log=True, zorder=2)
ax.set_xlabel(r"minimal residual $R_{\min}$")
ax.set_ylabel("hard primes (log scale)")
ax.set_xticks(xs)
ax.set_xticklabels([str(r) for r in xs], fontsize=7)
ax.tick_params(axis="y", labelsize=8)
ax.set_ylim(0.5, 2e8)
ax.annotate(
    r"record: unique prime $p = 8{,}803{,}369$",
    xy=(107, 1), xytext=(72, 2e3),
    arrowprops=dict(arrowstyle="->", lw=0.8),
    fontsize=8,
)
ax.spines["top"].set_visible(False)
ax.spines["right"].set_visible(False)
fig.tight_layout()
fig.savefig("fig_minR_hist.pdf")
print("wrote fig_minR_hist.pdf")
