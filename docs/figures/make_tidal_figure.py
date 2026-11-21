#!/usr/bin/env python3
"""Regenerate the tidal-eigenvalue figure for docs/Gravitation-Formalisation.md.

Frame eigenvalues of the Schwarzschild-de Sitter Riemann tensor, M = 1:

    angular   R_{t theta t theta} = M/r^3 - Lambda/3      (solid)
    radial    R_{t r t r}         = -2M/r^3 - Lambda/3    (dashed)

Dotted lines mark -Lambda/3, the common de Sitter offset.  No dependencies
beyond the standard library: it writes an SVG directly.
"""

rmin, rmax = 3.0, 12.0
vmin, vmax = -0.125, 0.05
W, H = 720, 430
L, R, T, B = 78, 150, 30, 56

LAMS = [(0.0, "#1f4e79"), (0.05, "#c55a11"), (0.1, "#548235")]


def X(r):
    return L + (r - rmin) / (rmax - rmin) * (W - L - R)


def Y(v):
    return T + (vmax - v) / (vmax - vmin) * (H - T - B)


def angular(lam, r):
    return 1.0 / r ** 3 - lam / 3.0


def radial(lam, r):
    return -2.0 / r ** 3 - lam / 3.0


def path(fn, lam, n=360):
    pts = []
    for i in range(n + 1):
        r = rmin + (rmax - rmin) * i / n
        pts.append(f"{X(r):.2f},{Y(fn(lam, r)):.2f}")
    return " ".join(pts)


out = []
out.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
           f'viewBox="0 0 {W} {H}">')
out.append('<rect width="100%" height="100%" fill="#ffffff"/>')
out.append('<g font-family="Georgia, \'Times New Roman\', serif" font-size="13" fill="#222">')

# grid and ticks
for v in (-0.12, -0.09, -0.06, -0.03, 0.0, 0.03):
    y = Y(v)
    out.append(f'<line x1="{L}" y1="{y:.2f}" x2="{W - R}" y2="{y:.2f}" '
               f'stroke="#e6e6e6" stroke-width="1"/>')
    out.append(f'<text x="{L - 10}" y="{y + 4:.2f}" text-anchor="end">{v:.2f}</text>')
for r in (3, 5, 7, 9, 12):
    x = X(r)
    out.append(f'<line x1="{x:.2f}" y1="{T}" x2="{x:.2f}" y2="{H - B}" '
               f'stroke="#f0f0f0" stroke-width="1"/>')
    out.append(f'<text x="{x:.2f}" y="{H - B + 20}" text-anchor="middle">{r}</text>')

# -Lambda/3 asymptotes
for lam, col in LAMS:
    y = Y(-lam / 3.0)
    out.append(f'<line x1="{L}" y1="{y:.2f}" x2="{W - R}" y2="{y:.2f}" '
               f'stroke="{col}" stroke-width="1" stroke-dasharray="1.5,4" opacity="0.85"/>')

# curves: angular solid, radial dashed
for lam, col in LAMS:
    out.append(f'<polyline points="{path(angular, lam)}" fill="none" stroke="{col}" '
               f'stroke-width="2.1"/>')
    out.append(f'<polyline points="{path(radial, lam)}" fill="none" stroke="{col}" '
               f'stroke-width="2.1" stroke-dasharray="6,4"/>')

# axes
out.append(f'<line x1="{L}" y1="{H - B}" x2="{W - R}" y2="{H - B}" stroke="#333" stroke-width="1.2"/>')
out.append(f'<line x1="{L}" y1="{T}" x2="{L}" y2="{H - B}" stroke="#333" stroke-width="1.2"/>')
out.append(f'<text x="{(L + W - R) / 2:.0f}" y="{H - 16}" text-anchor="middle" '
           f'font-size="14">r  (M = 1)</text>')
out.append(f'<text x="20" y="{(T + H - B) / 2:.0f}" text-anchor="middle" font-size="14" '
           f'transform="rotate(-90 20 {(T + H - B) / 2:.0f})">frame eigenvalue</text>')

# style legend
out.append(f'<rect x="{L + 12}" y="{T + 8}" width="248" height="54" fill="#ffffff" '
           f'fill-opacity="0.92" stroke="#bbb" stroke-width="0.8" rx="3"/>')
out.append(f'<line x1="{L + 22}" y1="{T + 26}" x2="{L + 54}" y2="{T + 26}" '
           f'stroke="#444" stroke-width="2.1"/>')
out.append(f'<text x="{L + 62}" y="{T + 30}">angular  M/r³ − Λ/3</text>')
out.append(f'<line x1="{L + 22}" y1="{T + 46}" x2="{L + 54}" y2="{T + 46}" '
           f'stroke="#444" stroke-width="2.1" stroke-dasharray="6,4"/>')
out.append(f'<text x="{L + 62}" y="{T + 50}">radial  −2M/r³ − Λ/3</text>')

# colour legend
x0 = W - R + 20
out.append(f'<text x="{x0}" y="{T + 16}" font-size="12" fill="#555">Λ</text>')
for k, (lam, col) in enumerate(LAMS):
    y = T + 40 + 26 * k
    out.append(f'<line x1="{x0}" y1="{y}" x2="{x0 + 22}" y2="{y}" stroke="{col}" stroke-width="2.5"/>')
    label = "0" if lam == 0 else f"{lam:g}"
    out.append(f'<text x="{x0 + 30}" y="{y + 4}">= {label}</text>')
out.append(f'<text x="{x0}" y="{T + 40 + 26 * 3 + 12}" font-size="12" fill="#555">'
           f'dotted: −Λ/3</text>')

out.append("</g></svg>")
open("tidal-eigenvalues.svg", "w").write("\n".join(out) + "\n")
print("wrote tidal-eigenvalues.svg")
