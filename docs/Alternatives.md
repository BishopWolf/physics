# Alternatives to General Relativity as Field Theories: A Formalisation Plan

**Alex Vergara Gil**

26 November 2026

> **Companion paper.** This is the fourth of the programme's papers. Paper I
> (`Gravitation-Formalisation.md`) records sixteen alternative and modified
> theories, but with uneven depth: some carry their field equations, while MOND,
> MOG and TeVeS remain structural statements. This paper's goal is to promote
> each alternative to a full field theory — action, field equations, weak-field
> limit, stability and cosmology — or to record precisely why it cannot be
> promoted. It is a plan; the present formalisation is the starting point it
> describes.

---

## Abstract

The development contains machine-checked material on modified gravity: the
deep-MOND relation and flat rotation curves, the bounded MOG enhancement, the
TeVeS disformal metric, Brans–Dicke and $f(R)$ field equations, chameleon
screening, Einstein–Aether, massive gravity, Kaluza–Klein, Lovelock,
Einstein–Cartan, teleparallel, Nordström, Galileon and PPN parameters. The
depth is uneven and stated per module. This paper sets a uniform standard: a
theory counts as formalised when its action, field equations, parameterised
post-Newtonian limit, degrees of freedom and background cosmology are all
machine-checked. It then goes through the alternatives one by one against that
standard, records what is already there and what each needs, and states the
verdict criterion. No alternative is claimed to be a full theory today.

**Keywords:** modified gravity · MOND · TeVeS · MOG · PPN · formal verification

---

## 1. The gap

Paper I's §4.6 says it plainly: Einstein–Cartan, teleparallel, Kaluza–Klein,
Lovelock, Einstein–Aether, massive gravity, PPN, Brans–Dicke/$f(R)$ and
chameleon screening carry their field equations or exact reductions, while
MOND, MOG and TeVeS remain structural, and the Galileon result is
one-dimensional. None is a full nonlinear solution theory, and empirical
strengths and weaknesses are prose, not theorems.

That is a defensible place to stop for a paper about general relativity, but it
is not a uniform standard. A reader cannot tell whether MOND fails to be a
field theory or simply has not been written down yet in this development.

## 2. The standard

An alternative is **promoted** when all of the following are machine-checked
statements about it, in the same tensor language as Papers I–II:

| Criterion | Content |
| --- | --- |
| V1 Action | A Lagrangian density and the resulting field equations, with the matter coupling explicit |
| V2 PPN limit | The post-Newtonian parameters $\gamma,\beta,\alpha_i,\zeta_i$ and their comparison with Solar-System bounds |
| V3 Stability | Degrees of freedom counted, ghosts and gradient instabilities excluded or exhibited |
| V4 Cosmology | Background equations and linear perturbations, with the expansion history recovered |
| V5 Filter | Gravitational-wave speed consistent with GW170817, $\lvert c_{gw}-c\rvert/c<10^{-15}$, where the theory predicts a speed |

V1–V4 are the promotion test; V5 is a filter that a viable theory must pass.
A theory that fails V1 remains a *shadow*; one that passes V1 but not V2–V4 is
*partial*.

## 3. The alternatives

Each entry states what is formalised now, what promotion needs, and the current
verdict under §2.

### 3.1 MOND

**Now.** The deep-MOND relation, the flat-rotation law `MOND.flat_rotation`, and
the acceleration scale, in `Gravitation.Relativity.General.Modified.MOND`.

**Needs.** A choice between modified inertia and a modified-gravity action
(AQUAL/quasi-linear), the field equation that produces the interpolating
function, lensing without dark matter, and a cosmological background.

**Verdict.** Shadow: kinematics only.

### 3.2 MOG / STVG

**Now.** The Yukawa-like enhancement $\Phi=-(GM/r)[1+\alpha(1-e^{-\mu r})]$ and
the bounded-enhancement statement, in `Modified.MOG`.

**Needs.** The massive-vector action, its field equations coupled to the
metric, the PPN parameters, and stability of the vector sector.

**Verdict.** Shadow: a potential, not a theory.

### 3.3 TeVeS

**Now.** The disformal physical metric with explicit inverse,
`TeVeS.metric_lorentzian` and `TeVeS.metric_spatial`, in `Modified.TeVeS`.

**Needs.** The full TeVeS action (metric, scalar, unit vector), the scalar and
vector field equations, the lensing prediction, and the cosmological
perturbation spectrum. The known constraints (GW speed, cluster lensing, CMB)
should then be checked rather than asserted.

**Verdict.** Shadow, but the closest to promotion: the geometric core exists.

### 3.4 Brans–Dicke

**Now.** The field equation, the Cassini bound on $\omega$, the
$\omega\to\infty$ limit and the ghost pole, in `Modified.BransDicke`.

**Needs.** The PPN map at finite $\omega$, the cosmological solution, and the
stability statement beyond the pole.

**Verdict.** Partial: field equations present.

### 3.5 f(R) gravity

**Now.** The algebraic field equation, the trace identity, the Starobinsky
potential, the scalar mass and the Einstein-frame plateau, in
`Modified.FRGravity`.

**Needs.** Well-posedness of the fourth-order system, the chameleon/screening
limit, and the perturbation equations used by Cosmology.

**Verdict.** Partial.

### 3.6 Chameleon screening

**Now.** The density–mass–range chain, Yukawa suppression, the thin-shell
factor, and the exterior profile with screened and unscreened fifth-force
bounds, in `Modified.ChameleonScreening`.

**Needs.** Embedding in a specific scalar–tensor action and the cosmological
evolution of the screening radius.

**Verdict.** Mechanism, not a theory on its own.

### 3.7 Einstein–Aether

**Now.** The aether field and its field equations in
`Modified.EinsteinAether`.

**Needs.** The PPN parameters, the linearised spectrum and the cosmological
background, plus the GW-speed constraint.

**Verdict.** Partial.

### 3.8 Massive gravity

**Now.** Fierz–Pauli, the vDVZ discontinuity and the dRGT mass term, in
`Modified.MassiveGravity.{FierzPauli,VDVZ,DRGT}`.

**Needs.** The nonlinear field equations, the absence of the Boulware–Deser
ghost, and the cosmological background.

**Verdict.** Partial.

### 3.9 Kaluza–Klein

**Now.** The five-dimensional metric, the Kaluza miracle and the gauge
transformation, in `Modified.KaluzaKlein.*`.

**Needs.** The full reduction of the five-dimensional Einstein equations,
including the scalar and the tower, and the PPN limit.

**Verdict.** Partial.

### 3.10 Lovelock gravity

**Now.** The Lovelock invariants and the generalised Kronecker symbol, in
`Modified.Lovelock.*`.

**Needs.** The field equations in $D\ge5$, their linearisation and the
cosmological solutions.

**Verdict.** Algebraic.

### 3.11 Einstein–Cartan

**Now.** Torsion and the Einstein–Cartan field equations, in
`Modified.EinsteinCartan`.

**Needs.** The spin-fluid coupling, the avoidance-of-singularity claim and the
perturbation theory.

**Verdict.** Partial.

### 3.12 Teleparallel gravity

**Now.** The tetrad formulation, $f(T)$ gravity and the FLRW torsion ansatz, in
`Modified.Teleparallel.*`.

**Needs.** The full $f(T)$ field equations, the extra degrees of freedom and
the PPN limit.

**Verdict.** Partial.

### 3.13 Nordström's theory

**Now.** The conformal metric, $S=-6\Box\phi/\phi^3$ and the Einstein–Fokker
equivalence, in `Modified.Nordstrom`.

**Needs.** Little: it is a complete, if empirically excluded, scalar theory.
The promotion here is to state its PPN parameters and its failure against
observation.

**Verdict.** Full as a toy theory; excluded observationally.

### 3.14 Galileon and Ostrogradsky

**Now.** The one-dimensional total-derivative and shift structure, the
degenerate velocity Hessian and the unbounded Hamiltonian, contrasted with a
positive-definite kinetic term, in `Modified.Galileon` and
`Modified.Ostrogradsky`.

**Needs.** The covariant Galileon action, its field equations and the
Vainshtein screening solution.

**Verdict.** Mechanism plus a no-go check.

### 3.15 PPN parameters

**Now.** The parameter dictionary in `Modified.PPNParameters`.

**Needs.** Nothing for promotion: PPN is the comparison framework V2, not a
theory. Its role is to receive the parameters from the sections above.

**Verdict.** Framework.

## 4. The order of work

1. Complete V1 for MOND, MOG and TeVeS — the three shadows.
2. Compute V2 for every theory that passes V1, using `Modified.PPNParameters`.
3. Audit V3, starting with the theories whose actions carry higher derivatives
   or vector sectors.
4. Add V4 for the theories that survive V2 and V3.
5. Apply V5 as a filter and record the verdicts in Paper I's alternatives
   section, demoting the prose that no longer matches its module.

## 5. What is not claimed

- No alternative is a full field theory in this development today.
- No observational data analysis: PPN bounds and GW170817 are cited as filters,
  not re-derived.
- No claim that a theory failing V1 is physically wrong; only that it is not
  formalised as a field theory here.
- No quantum-gravity embedding. The structural correspondences collected in
  `QUANTUM-GRAVITY-MAPPING.md` are classification, not derivation.

## 6. Relation to the other papers

Paper I owns the alternatives' current statements; this paper owns their
promotion. Paper II and the constraint paper are independent of this track.
`QUANTUM-GRAVITY-MAPPING.md` records which quantum-gravity programmes the
structures resemble; it is not part of the promotion test.

## 7. Reproducibility and trust

The standard gates apply unchanged: silent build, no `sorry` or `admit`, axiom
footprints inside $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$,
and a current `Proof-Status.md`. Any promoted statement is a theorem in the
`Gravitation` module, audited like the rest.

## References

1. M. Milgrom. *A modification of the Newtonian dynamics as a possible alternative to the hidden mass hypothesis.* ApJ 270 (1983) 365.
2. J. Bekenstein. *Relativistic gravitation theory for the modified Newtonian dynamics paradigm.* Phys. Rev. D 70 (2004) 083509.
3. J. W. Moffat. *Scalar–tensor–vector gravity theory.* JCAP 03 (2006) 004.
4. T. Clifton, P. G. Ferreira, A. Padilla, C. Skordis. *Modified gravity and cosmology.* Phys. Rept. 513 (2012) 1.
5. C. M. Will. *The confrontation between general relativity and experiment.* Living Rev. Relativ. 17 (2014) 4.
6. B. P. Abbott et al. *Gravitational waves and gamma-rays from a binary neutron star merger: GW170817 and GRB 170817A.* ApJL 848 (2017) L13.
7. C. Skordis, T. Złośnik. *New relativistic theory for modified Newtonian dynamics.* Phys. Rev. Lett. 127 (2021) 161302.
8. A. Vergara Gil. *Which modified-gravity theory matches which quantum-gravity approach?* `QUANTUM-GRAVITY-MAPPING.md`, 2026.
