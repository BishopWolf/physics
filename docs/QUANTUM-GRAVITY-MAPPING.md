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
| **Brans–Dicke** | **String theory** (dilaton/moduli), **Kaluza–Klein** | A massless scalar with a non-minimal `φR` coupling is exactly the dilaton sector: the string-frame action is Brans–Dicke with `ω = −1`. Moduli and KK radions are the same structure |
| **f(R), Starobinsky `R + αR²`** | **Inflationary cosmology in both string- and LQG-inspired programmes** | `R²` is the Starobinsky attractor, the best-fitting inflationary model alongside α-attractors; it appears as an `α'` correction in string theory and is added by hand in LQC-inspired cosmology. It is also Brans–Dicke with `ω = 0` |
| **Horndeski / Galileons** | **String theory** (DGP decoupling limit, `α'`/DBI expansions); screening mechanisms shared with emergent-gravity constructions | Horndeski is the most general scalar-tensor theory with second-order equations; Galileons arise in the DGP braneworld limit and give Vainshtein screening |
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

## Scalar–tensor and higher-order theories: where their UV completions point

Brans–Dicke, `f(R)` and Horndeski are not alternatives to each other so much as
nested families: `f(R)` is Brans–Dicke with `ω = 0`, and both are Horndeski
with particular `G₂…G₅`. Their QG status is correspondingly different from
MOND's: each has a *known* or *natural* UV home, but that home does not require
the theory to be fundamental.

### Brans–Dicke → the string dilaton

The string-frame low-energy action contains `e^{−2Φ}(R + 4(∂Φ)²)`. After the
conformal transformation to the Einstein frame this is a scalar with a
non-minimal coupling, i.e. a Brans–Dicke-type theory with `ω = −1` and a
potential generated by fluxes and non-perturbative effects. The same structure
appears for moduli and for the radion in Kaluza–Klein compactifications. This is
the cleanest UV completion of any theory in this repository — but it is a
completion of the *scalar sector*, not a prediction of a particular `ω`.

The Lean theorems pin the phenomenology: `BransDicke.gamma_bounds` (every
positive `ω` deviates from GR), `BransDicke.cassini_deviation` (the
`ω > 40000` bound) and `BransDicke.fR_gamma` (`ω = 0` gives `γ = 1/2`).

### f(R) → Starobinsky inflation, with both string and LQG contacts

`f(R) = R + αR²` is Starobinsky's model. It predicts
`n_s ≈ 1 − 2/N`, `r ≈ 12/N²`, which is among the best fits to the Planck data,
and its scalar is precisely the extra degree of freedom counted by
`fR.not_gr` with mass `fR.mass_sq`.

* In **string theory**, `R²` and higher curvature terms are `α'` corrections;
  they are the leading terms of the same expansion that produces Galileons.
* In **LQG-inspired cosmology**, `R²` terms are added to the effective action
  and quantised alongside the LQC bounce; Starobinsky inflation and LQC are
  often treated as compatible rather than competing.

The weakness is equally sharp: pure `f(R)` has `γ = 1/2`, excluded by
solar-system tests unless a chameleon/symmetron screening mechanism hides the
scalar in dense environments. Screening is a property of the potential and the
coupling, and is not formalised here.

### Horndeski and Galileons → DGP, string `α'` expansion, and screening

Horndeski's theorem — that the `G₂…G₅` Lagrangian is the most general
scalar-tensor action with second-order field equations — is the structural
statement that makes the family ghost-free. Galileons are its shift-symmetric
members; they arise in the DGP braneworld decoupling limit and in the `α'`/DBI
expansions of string theory.

The Lean module proves the one-dimensional core of the mechanism:
`Galileon.cubic_total_derivative` (the cubic density is a total derivative),
`Galileon.shift_total_derivative` (shift symmetry holds up to a total
derivative) and `Galileon.shift_forbids_potential` (so the scalar cannot have a
mass term). Those are exactly the properties that keep the equations second
order and remove the Ostrogradsky ghost.

The empirical weakness is now observational rather than theoretical: GW170817
requires `|c_gw − c|/c < 10^{-15}`, which for Horndeski forces `G₄` to be
nearly independent of `X` (and `G₅` constant). That eliminates most
dark-energy Galileon models, though not the screening mechanism or the
Early-Dark-Energy variants. Nothing in the Lean development can express that
constraint; it is an empirical bound, recorded here as such.

### Ostrogradsky: why the family boundaries are sharp

Generic higher-derivative Lagrangians — `f(R, Ric², Riem²)`, or any action with
non-degenerate dependence on second derivatives — have fourth-order equations
and therefore a ghost (Ostrogradsky 1850). `f(R)` escapes because it is
Brans–Dicke with `ω = 0`, a healthy scalar; Horndeski escapes by construction.
This is the reason the three families above are the viable ones and the reason
higher-order corrections in string theory must come with a UV completion that
removes the ghost. The Lean development does not formalise Ostrogradsky's
theorem; it formalises the shift-symmetry and total-derivative structure that
Horndeski's escape relies on.

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
