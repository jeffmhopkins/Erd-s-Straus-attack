"""Regenerate fig_minR_hist.pdf (Figure 1 of the paper).

Log-scale histogram of the minimal-residual distribution over all
1,175,215,396 hard primes below 10^12, from the distribution of
Table 3 (data/hard_primes_1e12_minimalR.*). The figure is built at
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

# Table 3 of the paper (10^12 data).
DIST = {
    3: 657645152, 7: 286441544, 11: 167419973, 15: 33222834, 19: 19307426,
    23: 7996742, 27: 1376271, 31: 1318258, 35: 208713, 39: 160273,
    43: 43558, 47: 50190, 51: 8756, 55: 7441, 59: 4863, 63: 1439, 67: 488,
    71: 970, 75: 146, 79: 208, 83: 78, 87: 40, 91: 5, 95: 12, 99: 4,
    103: 5, 107: 4, 111: 3,
}

fig, ax = plt.subplots(figsize=(6.3, 3.4))
xs = list(DIST.keys())
ys = [DIST[r] for r in xs]
# The band 87-103 was empty below 10^10 (Section 6.1 of the paper).
ax.axvspan(85, 113, color="0.88", zorder=0)
ax.text(99, 6e6, "band empty\nbelow $10^{10}$", ha="center",
        fontsize=8, color="0.35")
ax.bar(xs, ys, width=3.0, color="#3b5b92", edgecolor="black",
       linewidth=0.4, log=True, zorder=2)
ax.set_xlabel(r"minimal residual $R_{\min}$")
ax.set_ylabel("hard primes (log scale)")
ax.set_xticks(xs)
ax.set_xticklabels([str(r) for r in xs], fontsize=7)
ax.tick_params(axis="y", labelsize=8)
ax.set_ylim(0.5, 2e9)
ax.annotate(
    r"record $R=111$: $p = 119{,}945{,}383{,}009$",
    xy=(111, 3), xytext=(70, 3e3),
    arrowprops=dict(arrowstyle="->", lw=0.8),
    fontsize=8,
)
ax.spines["top"].set_visible(False)
ax.spines["right"].set_visible(False)
fig.tight_layout()
fig.savefig("fig_minR_hist.pdf")
print("wrote fig_minR_hist.pdf")
