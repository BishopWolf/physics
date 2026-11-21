# Which modified-gravity theory matches which quantum-gravity approach?

Short answer: **none of MOND, TeVeS or MOG is derived from a UV-complete theory
of quantum gravity.** They are phenomenological responses to galactic-scale
data. What can be said precisely is which *structures* each one shares with
which QG/unification programme, and that is what this note records. Everything
below is a classification by structural resemblance, not a derivation; none of
these correspondences is a theorem, and none should be read as evidence that the
QG candidate in question predicts the modified dynamics.

## Summary table

| Modified gravity | Closest QG / unification family | Structural reason |
| --- | --- | --- |
| **MOND** (Milgrom 1983) | **Emergent / entropic gravity** (Jacobson 1995; Verlinde 2016) | `a₀ ~ cH₀`; MOND-scale acceleration emerges from horizon thermodynamics / elastic dark-energy response; no fundamental new field |
| **TeVeS** (Bekenstein 2004) | **Einstein–aether → Hořava–Lifshitz** (emergent-gravity family); **bimetric/massive gravity** via the disformal metric | TeVeS carries a unit timelike vector — literally an aether field; the physical metric is disformally related to the Einstein metric, a bimetric structure |
| **MOG / STVG** (Moffat 2006) | **Massive gravity** (dRGT) and **Einstein–aether**; string-motivated massive vectors (KK) at a stretch | A massive vector mediates a Yukawa enhancement of the Newtonian potential; the closest healthy relativistic relatives are massive-gravity/aether theories |
| — | **String theory** | No direct match. String vacua reduce to GR plus matter; the nearest ingredients are galileons (DGP decoupling limit) and Kaluza–Klein massive gravitons. Galileon/Vainshtein screening is the closest *mechanism* to MOG's short-distance enhancement and TeVeS's screening |
| — | **Loop quantum gravity** | No established match. LQG quantises GR and has GR as its semiclassical limit; its modifications are Planck-scale (and in cosmology, LQC bounces), not galactic |

## Why MOND points at emergent gravity

MOND's single constant has the dimensions of an acceleration and numerically
satisfies `a₀ ≈ cH₀/(2π)` (up to order-one factors). That coincidence is the
reason MOND is naturally read as a *thermodynamic* or *emergent* effect rather
than a new force:

* Jacobson (1995) derives the Einstein equations from horizon thermodynamics;
  the derivation fixes the Einstein coupling but not `a₀`.
* Verlinde (2016) argues that baryonic mass displaces dark energy, producing an
  elastic response whose acceleration scale is `cH₀`, reproducing the MOND
  relation and the baryonic Tully–Fisher law `v⁴ = G M a₀` (the theorem
  `MOND.flat_rotation` in this repository is the kinematic core of that law).
* Milgrom's "modified inertia" variant is likewise kinematical/Unruh-flavoured,
  which is why analogue-gravity and Unruh-effect language appears in that
  literature.

Caveat: Verlinde's derivation is not a QG completion, and its assumptions
(holographic dark energy, elastic medium) are contested.

## Why TeVeS points at Einstein–aether and Hořava–Lifshitz

TeVeS is a *relativistic* MOND: a metric, a scalar `φ` and a unit timelike
vector `U`, with the physical (Jordan) metric built disformally,

`g̃ = e^{−2φ}(g + U ⊗ U) − e^{2φ} U ⊗ U`.

Two structures are decisive:

* `U` with `g(U,U) = −1` is exactly an **Einstein–aether** field
  (Jacobson–Mattingly 2001). Einstein–aether is the IR limit of
  **Hořava–Lifshitz gravity**, the canonical "emergent/condensed-matter"
  quantum-gravity proposal with anisotropic scaling.
* The disformal relation between `g` and `g̃` is a **bimetric** structure,
  connecting TeVeS to bimetric and massive-gravity constructions.

The Lean module proves the property that makes this reading consistent:
`TeVeS.metric_lorentzian` — the physical metric stays Lorentzian for every `φ`,
so the aether/disformal map does not destroy causal structure. It also proves
`TeVeS.metric_spatial`, the conformal rescaling `e^{−2φ}δ` through which TeVeS
produces lensing without dark matter.

Caveat: the original TeVeS is strongly constrained (gravitational-wave speed,
cluster lensing, CMB); relativistic MOND has since moved to constructions such
as RMOND (Skordis–Złośnik 2021), which fits the CMB but is a further step away
from any QG embedding.

## Why MOG points at massive gravity

MOG (a.k.a. STVG) adds a massive vector field whose effect is a Yukawa-like
modification,

`Φ = −(GM/r)[1 + α(1 − e^{−μr})]`,

with `α` a strength and `μ` an inverse range. A massive vector mediating a
finite-range enhancement is the same ingredient that appears in:

* **massive gravity** (Fierz–Pauli; dRGT), where a graviton mass gives a
  Yukawa-type correction with the vDVZ/Vainshtein screening problem;
* **Einstein–aether**, where a timelike vector acquires an effective mass;
* string compactifications producing **Kaluza–Klein massive gravitons**, at the
  level of the field content only.

The Lean module proves the structural ceiling that any such single-range
Yukawa has: `MOG.factor_bounds` — the enhancement lies in `[1, 1 + α]` — and
`MOG.factor_zero`, that it is exactly `1` at `r = 0`. This is why MOG needs
`α` retuned between galaxies and clusters: a single `α` cannot cover a larger
mass discrepancy.

## String theory: no direct match

String theory's low-energy limit is ordinary GR with matter, and its
modifications are either ultraviolet (string scale) or extra-dimensional. The
closest contact points are indirect:

* **Galileons** (Nicolis–Rattazzi–Trincherini 2009), which arise in the DGP
  braneworld decoupling limit, give derivative self-interactions and Vainshtein
  screening — the same *screening* phenomenon that MOG's Yukawa and TeVeS's
  scalar mimic.
* **DGP** itself (Dvali–Gabadadze–Porrati 2000) modifies gravity in the
  infrared, but on cosmological rather than galactic scales, and does not
  reproduce MOND.
* **Kaluza–Klein massive gravitons** share the field content of MOG's massive
  vector, not its dynamics.

No string construction is known that yields MOND, TeVeS or MOG as a
low-energy limit.

## Loop quantum gravity: no established match

LQG is a canonical quantisation of GR. Its classical limit is GR, its
modifications are Planck-scale (area/discrete geometry) or early-universe
(loop quantum cosmology bounces), and it contains no preferred acceleration
scale. There is no standard LQG-derived MOND, TeVeS or MOG; claims otherwise
are speculative and are not part of the mainstream LQG literature.

## What would turn a resemblance into a derivation

For any of these correspondences to become more than a classification, one would
need a controlled limit in which the QG candidate produces:

1. the MOND scale `a₀` with its observed value, not as an input;
2. the interpolating function `μ` (or an equivalent) from the same dynamics;
3. the correct lensing and gravitational-wave speed (the GW170817 constraint
   `|c_gw − c|/c < 10^{-15}` is the sharpest existing filter);
4. cluster-scale and cosmological behaviour without retuning `α`, `μ` or `a₀`.

None of the four is currently satisfied by any of the three theories from a QG
starting point. The Lean theorems in `Gravitation.Alternatives` formalise the
structure that such a derivation would have to reproduce — the flat-rotation
law, the enhancement bound, the preserved signature — not the derivation itself.

## References

* M. Milgrom, ApJ 270 (1983) 365.
* J. D. Bekenstein, PRD 70 (2004) 083509 (TeVeS).
* J. W. Moffat, JCAP 0603 (2006) 004 (MOG/STVG).
* T. Jacobson, PRL 75 (1995) 1260.
* E. Verlinde, SciPost Phys. 2 (2017) 016.
* T. Jacobson & D. Mattingly, PRD 64 (2001) 024028 (Einstein–aether).
* P. Hořava, PRD 79 (2009) 084008.
* G. Dvali, G. Gabadadze, M. Porrati, PLB 485 (2000) 208 (DGP).
* A. Nicolis, R. Rattazzi, E. Trincherini, PRD 79 (2009) 064036 (galileons).
* C. de Rham, G. Gabadadze, A. Tolley, PRL 106 (2011) 231101 (dRGT).
* C. Skordis & T. Złośnik, PRL 127 (2021) 161302 (RMOND).
* T. Clifton, P. Ferreira, A. Padilla, C. Skordis, Phys. Rept. 513 (2012) 1.
* A. Ashtekar & J. Lewandowski, CQG 21 (2004) R53 (LQG review).
* B. P. Abbott et al., ApJL 848 (2017) L13 (GW170817).
