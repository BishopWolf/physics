# Alternatives to General Relativity as Field Theories: A Formalisation Plan

**Alex Vergara Gil**

26 November 2026

> **Companion paper.** This is the fourth of four accounts. The first
> (`Gravitation-Formalisation.md`) records sixteen alternative and modified
> theories, but with uneven depth: some carry their field equations, while MOND,
> MOG and TeVeS remain structural statements. This paper's goal is to promote
> each alternative to a full field theory — action, field equations, weak-field
> limit, stability and cosmology — or to record precisely why it cannot be
> promoted. It is a plan; the present development is the starting point it
> describes.

---

## Abstract

The development contains machine-checked material on modified gravity: the
deep-MOND relation and flat rotation curves, the bounded MOG enhancement, the
TeVeS disformal metric, Brans–Dicke and $f(R)$ field equations, chameleon
screening, Einstein–Aether, massive gravity, Kaluza–Klein, Lovelock,
Einstein–Cartan, teleparallel, Nordström, Galileon and PPN parameters. The
depth is uneven. This paper sets a uniform standard: a theory counts as
formalised when its action, field equations, parameterised post-Newtonian
limit, degrees of freedom and background cosmology are all machine-checked. It
goes through the alternatives one by one against that standard, records what is
already there and what each needs, and states the verdict criterion. MOND, MOG and TeVeS
now carry stated actions and field equations; no derivation of a field equation
from its action is formalised. No alternative is claimed to be a full theory
today.

**Keywords:** modified gravity · MOND · TeVeS · MOG · PPN · formal verification

---

## 1. The gap

The first paper says it plainly: Einstein–Cartan, teleparallel, Kaluza–Klein,
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
statements about it:

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

**Now.** The deep-MOND relation, the flat-rotation law and the acceleration
scale. The AQUAL action density
$-(a_0^2/8\pi G)F(|\nabla\phi|^2/a_0^2)-\rho\phi$ and the field equation
$\nabla\cdot[\mu(|\nabla\phi|/a_0)\nabla\phi]=4\pi G\rho$ are stated, with the
interpolating function $\mu(x)=x/\sqrt{1+x^2}$ and the Poisson limit at
$\mu=1$.

**Needs.** The derivation of the field equation from the action, the
interpolating function selected by the action's free function, lensing without
dark matter, and a cosmological background.

**Verdict.** V1 stated, not derived: the closest of the shadows to promotion.

### 3.2 MOG / STVG

**Now.** The Yukawa-like enhancement
$\Phi=-(GM/r)[1+\alpha(1-e^{-\mu r})]$ and the bounded-enhancement statement.
The gravitational sector of the STVG action — Einstein term, Proca mass term
and scalar potential — and the Proca field equation are also stated.

**Needs.** The massive-vector action, its field equations coupled to the
metric, the PPN parameters, and stability of the vector sector.

**Verdict.** V1 stated (action and Proca equation); PPN, stability and
cosmology absent, so partial.

### 3.3 TeVeS

**Now.** The disformal physical metric with explicit inverse; the physical
metric is shown to stay Lorentzian for every scalar, and its spatial part is a
conformal rescaling. The action density with the aether-projected scalar
kinetic term, and the scalar and Einstein field equations, are stated.

**Needs.** The full TeVeS action (metric, scalar, unit vector), the scalar and
vector field equations, the lensing prediction, and the cosmological
perturbation spectrum. The known constraints (GW speed, cluster lensing, CMB)
should then be checked rather than asserted.

**Verdict.** V1 stated: the geometric core and the action now exist; the
derivation and the PPN limit do not.

### 3.4 Brans–Dicke

**Now.** The field equation, the Cassini bound on $\omega$, the
$\omega\to\infty$ limit and the ghost pole.

**Needs.** The PPN map at finite $\omega$, the cosmological solution, and the
stability statement beyond the pole.

**Verdict.** Partial: field equations present.

### 3.5 f(R) gravity

**Now.** The algebraic field equation, the trace identity, the Starobinsky
potential, the scalar mass and the Einstein-frame plateau.

**Needs.** Well-posedness of the fourth-order system, the chameleon/screening
limit, and the perturbation equations used by cosmology.

**Verdict.** Partial.

### 3.6 Chameleon screening

**Now.** The density–mass–range chain, Yukawa suppression, the thin-shell
factor, and the exterior profile with screened and unscreened fifth-force
bounds.

**Needs.** Embedding in a specific scalar–tensor action and the cosmological
evolution of the screening radius.

**Verdict.** Mechanism, not a theory on its own.

### 3.7 Einstein–Aether

**Now.** The aether field and its field equations.

**Needs.** The PPN parameters, the linearised spectrum and the cosmological
background, plus the GW-speed constraint.

**Verdict.** Partial.

### 3.8 Massive gravity

**Now.** Fierz–Pauli, the vDVZ discontinuity and the dRGT mass term.

**Needs.** The nonlinear field equations, the absence of the Boulware–Deser
ghost, and the cosmological background.

**Verdict.** Partial.

### 3.9 Kaluza–Klein

**Now.** The five-dimensional metric, the Kaluza miracle and the gauge
transformation.

**Needs.** The full reduction of the five-dimensional Einstein equations,
including the scalar and the tower, and the PPN limit.

**Verdict.** Partial.

### 3.10 Lovelock gravity

**Now.** The Lovelock invariants and the generalised Kronecker symbol.

**Needs.** The field equations in $D\ge5$, their linearisation and the
cosmological solutions.

**Verdict.** Algebraic.

### 3.11 Einstein–Cartan

**Now.** Torsion and the Einstein–Cartan field equations.

**Needs.** The spin-fluid coupling, the avoidance-of-singularity claim and the
perturbation theory.

**Verdict.** Partial.

### 3.12 Teleparallel gravity

**Now.** The tetrad formulation, $f(T)$ gravity and the FLRW torsion ansatz.

**Needs.** The full $f(T)$ field equations, the extra degrees of freedom and
the PPN limit.

**Verdict.** Partial.

### 3.13 Nordström's theory

**Now.** The conformal metric, $S=-6\Box\phi/\phi^3$ and the Einstein–Fokker
equivalence.

**Needs.** Little: it is a complete, if empirically excluded, scalar theory.
The promotion here is to state its PPN parameters and its failure against
observation.

**Verdict.** Full as a toy theory; excluded observationally.

### 3.14 Galileon and Ostrogradsky

**Now.** The one-dimensional total-derivative and shift structure, the
degenerate velocity Hessian and the unbounded Hamiltonian, contrasted with a
positive-definite kinetic term.

**Needs.** The covariant Galileon action, its field equations and the
Vainshtein screening solution.

**Verdict.** Mechanism plus a no-go check.

### 3.15 PPN parameters

**Now.** The parameter dictionary.

**Needs.** Nothing for promotion: PPN is the comparison framework V2, not a
theory. Its role is to receive the parameters from the sections above.

**Verdict.** Framework.

## 4. The order of work

1. Derive the AQUAL field equation from the action, closing MOND's V1.
2. Derive the STVG and TeVeS field equations from their actions, adding the
   vector and scalar stress to the Einstein equation.
3. Compute V2 for every theory that passes V1, using the PPN dictionary.
4. Audit V3, starting with the theories whose actions carry higher derivatives
   or vector sectors.
5. Add V4 for the theories that survive V2 and V3.
6. Apply V5 as a filter and record the verdicts in the first paper's
   alternatives section, demoting prose that no longer matches.

## 5. What is not claimed

- No alternative is a full field theory in this development today.
- The AQUAL, STVG and TeVeS field equations are stated, not derived from their
  actions.
- No observational data analysis: PPN bounds and GW170817 are cited as filters,
  not re-derived.
- No claim that a theory failing V1 is physically wrong; only that it is not
  formalised as a field theory here.
- No quantum-gravity embedding. The structural correspondences in
  `QUANTUM-GRAVITY-MAPPING.md` are classification, not derivation.

## 6. Relation to the other papers

The first paper owns the alternatives' current statements; this paper owns their
promotion. The Cauchy and constraint papers are independent of this track.
The quantum-gravity mapping note records which programmes the structures
resemble; it is not part of the promotion test.

## 7. Reproducibility and trust

The development's build, axiom and proof-status checks apply unchanged. Any
promoted statement is fully proved like the rest, with no axiom of its own.

## References

1. M. Milgrom. *A modification of the Newtonian dynamics as a possible alternative to the hidden mass hypothesis.* ApJ 270 (1983) 365.
2. J. Bekenstein, M. Milgrom. *Does the missing mass problem signal the breakdown of Newtonian gravity?* ApJ 286 (1984) 7.
3. J. Bekenstein. *Relativistic gravitation theory for the modified Newtonian dynamics paradigm.* Phys. Rev. D 70 (2004) 083509.
4. J. W. Moffat. *Scalar–tensor–vector gravity theory.* JCAP 03 (2006) 004.
5. T. Clifton, P. G. Ferreira, A. Padilla, C. Skordis. *Modified gravity and cosmology.* Phys. Rept. 513 (2012) 1.
6. C. M. Will. *The confrontation between general relativity and experiment.* Living Rev. Relativ. 17 (2014) 4.
7. B. P. Abbott et al. *Gravitational waves and gamma-rays from a binary neutron star merger: GW170817 and GRB 170817A.* ApJL 848 (2017) L13.
8. C. Skordis, T. Złośnik. *New relativistic theory for modified Newtonian dynamics.* Phys. Rev. Lett. 127 (2021) 161302.
