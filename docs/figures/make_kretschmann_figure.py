#!/usr/bin/env python3
"""Regenerate the Kretschmann-comparison figure for the article.

For Schwarzschild-de Sitter the Weyl part of the curvature is Lambda
independent and the trace part contributes (8/3) Lambda^2, so

    K(r) = 48 M^2 / r^6 + (8/3) Lambda^2.

Writes an SVG directly; no dependencies beyond the standard library.
"""

rmin, rmax = 3.0, 12.0
kmin, kmax = 0.0, 0.10
W, H = 720, 430
L, R, T, B = 82, 150, 30, 56

LAMS = [(0.0, "#1f4e79"), (0.05, "#c55a11"), (0.1, "#548235")]


def X(r):
    return L + (r - rmin) / (rmax - rmin) * (W - L - R)


def Y(k):
    return T + (kmax - k) / (kmax - kmin) * (H - T - B)


def kretschmann(lam, r):
    return 48.0 / r ** 6 + (8.0 / 3.0) * lam ** 2


def weyl(r):
    return 48.0 / r ** 6


def path(fn, lam, n=360):
    pts = []
    for i in range(n + 1):
        r = rmin + (rmax - rmin) * i / n
        pts.append(f"{X(r):.2f},{Y(fn(lam, r)):.2f}")
    return " ".join(pts)


def flat(fn, n=360):
    pts = []
    for i in range(n + 1):
        r = rmin + (rmax - rmin) * i / n
        pts.append(f"{X(r):.2f},{Y(fn(r)):.2f}")
    return " ".join(pts)


out = []
out.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">')
out.append('<rect width="100%" height="100%" fill="#ffffff"/>')
out.append('<g font-family="Georgia, \'Times New Roman\', serif" font-size="13" fill="#222">')

for k in (0.0, 0.02, 0.04, 0.06, 0.08, 0.10):
    y = Y(k)
    out.append(f'<line x1="{L}" y1="{y:.2f}" x2="{W - R}" y2="{y:.2f}" stroke="#e6e6e6" stroke-width="1"/>')
    out.append(f'<text x="{L - 10}" y="{y + 4:.2f}" text-anchor="end">{k:.2f}</text>')
for r in (3, 5, 7, 9, 12):
    x = X(r)
    out.append(f'<line x1="{x:.2f}" y1="{T}" x2="{x:.2f}" y2="{H - B}" stroke="#f0f0f0" stroke-width="1"/>')
    out.append(f'<text x="{x:.2f}" y="{H - B + 20}" text-anchor="middle">{r}</text>')

# (8/3) Lambda^2 asymptotes
for lam, col in LAMS:
    y = Y((8.0 / 3.0) * lam ** 2)
    out.append(f'<line x1="{L}" y1="{y:.2f}" x2="{W - R}" y2="{y:.2f}" stroke="{col}" '
               'stroke-width="1" stroke-dasharray="1.5,4" opacity="0.9"/>')

for lam, col in LAMS:
    out.append(f'<polyline points="{path(kretschmann, lam)}" fill="none" stroke="{col}" stroke-width="2.2"/>')

# Weyl-only invariant: 48 M^2 / r^6
out.append(f'<polyline points="{flat(weyl)}" fill="none" stroke="#555" stroke-width="1.6" stroke-dasharray="6,4"/>')

out.append(f'<line x1="{L}" y1="{H - B}" x2="{W - R}" y2="{H - B}" stroke="#333" stroke-width="1.2"/>')
out.append(f'<line x1="{L}" y1="{T}" x2="{L}" y2="{H - B}" stroke="#333" stroke-width="1.2"/>')
out.append(f'<text x="{(L + W - R) / 2:.0f}" y="{H - 16}" text-anchor="middle" font-size="14">r  (M = 1)</text>')
out.append(f'<text x="20" y="{(T + H - B) / 2:.0f}" text-anchor="middle" font-size="14" '
           f'transform="rotate(-90 20 {(T + H - B) / 2:.0f})">Kretschmann  K</text>')

# style legend
out.append(f'<rect x="{L + 12}" y="{T + 8}" width="286" height="72" fill="#ffffff" fill-opacity="0.93" '
           'stroke="#bbb" stroke-width="0.8" rx="3"/>')
out.append(f'<line x1="{L + 22}" y1="{T + 24}" x2="{L + 54}" y2="{T + 24}" stroke="#444" stroke-width="2.2"/>')
out.append(f'<text x="{L + 62}" y="{T + 28}">K = 48M²/r⁶ + 8Λ²/3</text>')
out.append(f'<line x1="{L + 22}" y1="{T + 44}" x2="{L + 54}" y2="{T + 44}" stroke="#555" stroke-width="1.6" stroke-dasharray="6,4"/>')
out.append(f'<text x="{L + 62}" y="{T + 48}">Weyl part  48M²/r⁶</text>')
out.append(f'<line x1="{L + 22}" y1="{T + 64}" x2="{L + 54}" y2="{T + 64}" stroke="#444" stroke-width="1" stroke-dasharray="1.5,4"/>')
out.append(f'<text x="{L + 62}" y="{T + 68}">floor  8Λ²/3</text>')

x0 = W - R + 20
out.append(f'<text x="{x0}" y="{T + 16}" font-size="12" fill="#555">Λ</text>')
for k, (lam, col) in enumerate(LAMS):
    y = T + 40 + 26 * k
    out.append(f'<line x1="{x0}" y1="{y}" x2="{x0 + 22}" y2="{y}" stroke="{col}" stroke-width="2.5"/>')
    label = "0" if lam == 0 else f"{lam:g}"
    out.append(f'<text x="{x0 + 30}" y="{y + 4}">= {label}</text>')

out.append("</g></svg>")
open("kretschmann.svg", "w").write("\n".join(out) + "\n")
print("wrote kretschmann.svg")
