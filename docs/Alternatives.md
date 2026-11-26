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
now carry stated actions and field equations; the AQUAL Euler-Lagrange residual
is assembled in a one-dimensional model, but no full derivation from an action
is formalised. No alternative is claimed to be a full theory today.

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

**Needs.** The chain-rule evaluation of the two partial derivatives and the
functional-analytic minimisation behind the derivation, the interpolating
function selected by the action's free function, lensing without dark matter,
and a cosmological background.

**Verdict.** V1 stated, with the Euler-Lagrange residual assembled and
stationarity proved equivalent to the field equation in a one-dimensional
model; the chain rule is the remaining gap. The best developed of the three.

**PPN and degrees of freedom.** See §3.16–3.17.

### 3.2 MOG / STVG

**Now.** The Yukawa-like enhancement
$\Phi=-(GM/r)[1+\alpha(1-e^{-\mu r})]$ and the bounded-enhancement statement.
The gravitational sector of the STVG action — Einstein term, Proca mass term
and scalar potential — and the Proca field equation are also stated.

**Needs.** The massive-vector action, its field equations coupled to the
metric, the PPN parameters, and stability of the vector sector.

**Verdict.** V1 stated (action and Proca equation); PPN, stability and
cosmology absent, so partial.

**PPN and degrees of freedom.** See §3.16–3.17.

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

**PPN and degrees of freedom.** See §3.16–3.17.

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

### 3.16 PPN parameters of the three candidates

The parameterised post-Newtonian expansion compares a metric theory with the
Solar-System data through $\gamma$, $\beta$, the preferred-frame parameters
$\alpha_1,\alpha_2$, and the Whitehead and conservation parameters $\xi$,
$\zeta_i$, $\alpha_3$. The values below are collected from the literature; none
is re-derived here, and none is machine-checked.

| Theory | $\gamma$ | $\beta$ | $\alpha_1$ | $\alpha_2$ | $\alpha_3,\xi,\zeta_i$ | Status |
| --- | --- | --- | --- | --- | --- | --- |
| MOND (non-relativistic) | — | — | — | — | — | not a metric theory; PPN requires a relativistic completion |
| MOG / STVG | $1$ in the Moffat–Toth treatment, $1/3$ in the Deng–Xie–Huang treatment | theory-dependent | generically nonzero | generically nonzero | not all determined | contested; the vector couples to matter, so the Einstein equivalence principle fails and the standard PPN map is conditional |
| TeVeS | $1$ | $1$ | generically nonzero, $\lvert\alpha_1\rvert\lesssim10^{-4}$ | generically nonzero, $\lvert\alpha_2\rvert\lesssim4\times10^{-7}$ | $\alpha_3=\xi=\zeta_i=0$ | passes $\gamma$ and $\beta$; the preferred-frame parameters constrain the vector sector |

For TeVeS, Bekenstein's original calculation gives $\gamma=1$ for the physical
metric, and $\beta=1$ after the erratum; Tamaki's general treatment confirms
$\gamma=1$, $\beta=1$ under the assumption that both metrics are Minkowski at
zeroth order, and finds $\alpha_3=\xi=\zeta_i=0$. The preferred-frame
parameters were computed by Sagi: they are generically nonzero even when the
vector coupling is switched off, because matter couples to the disformal
metric rather than to the Einstein metric. Solar-System bounds
($\lvert\alpha_1\rvert\lesssim10^{-4}$,
$\lvert\alpha_2\rvert\lesssim4\times10^{-7}$) therefore constrain the vector
sector rather than being automatic.

For MOG the situation is unsettled. The Moffat–Toth treatment reports
$\gamma=1$; Deng, Xie and Huang report $\gamma=1/3$ in a scheme where the
vector field is kept but the PPN potentials are not extended, and the dispute
has not been resolved in the literature. Because the vector couples
universally to matter, STVG violates the Einstein equivalence principle, and
the standard PPN formalism - which assumes it - does not apply without
qualification.

MOND itself has no PPN parameters. AQUAL is a non-relativistic potential
theory; any $\gamma$ or $\beta$ attributed to MOND belongs to a relativistic
completion such as TeVeS or a newer construction, not to the AQUAL action.

### 3.17 Degrees of freedom and ghosts

| Theory | Tensor | Vector | Scalar | Total | Status |
| --- | --- | --- | --- | --- | --- |
| General relativity | 2 | — | — | 2 | — |
| STVG | 2 | 3 (massive Proca) | 1 for $G$, plus 1 if the vector mass $\mu$ is dynamical | 6 (7) | Proca sector ghost-free; the scalar needs a positive kinetic term and a bounded potential; no nonlinear Hamiltonian analysis is available |
| TeVeS | 2 | 3 (constrained unit timelike) | 1 | 6 | claimed ghost-free in the Hamiltonian analysis of Skordis–Złośnik; other analyses report a linear instability of the Schwarzschild–TeVeS solution, caustic formation in the vector field, and superluminal scalar modes for some parameter choices |

The counts are field-content counts, not the outcome of a Dirac constraint
analysis: a constrained vector contributes three degrees of freedom, a massive
vector also three, and the metric two. The TeVeS vector is normalised with
respect to the Einstein metric, so its timelike component is not independent;
the scalar is unconstrained.

For STVG, the vector is a Proca field: its kinetic term is the Maxwell term
with a mass, which has no ghost at the quadratic level, and the scalar sector
is ghost-free provided its kinetic term has the standard sign and its potential
is bounded below. The known problem is not a ghost but the violation of the
equivalence principle and the resulting preferred-frame effects. No full
nonlinear Hamiltonian analysis of STVG is available to cite either way.

For TeVeS the literature is divided. The Hamiltonian analysis of Skordis and
Złośnik finds no ghosts, and the vector and scalar together add two dynamical
degrees of freedom to the two tensor modes. Seifert finds that the
Schwarzschild–TeVeS solution is linearly unstable for parameters in the
phenomenologically allowed range; Contaldi, Wiseman and Withers show that the
Maxwell-type vector action develops caustics; and Sagi finds that the
cosmological value of the scalar forces it negative, making scalar waves
superluminal. These are not all ghosts, but they are dynamical pathologies, and
they are why TeVeS is listed as partial rather than promoted.

## 4. The order of work

1. Extend the AQUAL derivation from the one-dimensional model to variations of
   the full action, with the compact-support and integration-by-parts steps.
2. Derive the STVG and TeVeS field equations from their actions, adding the
   vector and scalar stress to the Einstein equation.
3. Compute V2 for every theory that passes V1, using the PPN dictionary.
4. Audit V3, starting with the theories whose actions carry higher derivatives
   or vector sectors. The literature audit of §3.17 is the starting point; a
   Dirac or Hamiltonian analysis is new work.
5. Add V4 for the theories that survive V2 and V3.
6. Apply V5 as a filter and record the verdicts in the first paper's
   alternatives section, demoting prose that no longer matches.

## 5. What is not claimed

- No alternative is a full field theory in this development today.
- The Euler-Lagrange residual of the AQUAL action is assembled and stationarity
  is proved to be the MOND equation in a one-dimensional model; the chain-rule
  evaluation of the partial derivatives is not formalised; the STVG and TeVeS
  equations are stated, not derived from their actions.
- The PPN values and degree-of-freedom counts of §3.16–3.17 are collected from
  the literature. None is re-derived, and none is machine-checked; a
  preferred-frame or ghost computation in this development would be new work.
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
9. T. Tamaki. *Post-Newtonian parameters in the tensor-vector-scalar theory.* Phys. Rev. D 77 (2008) 124020. arXiv:0803.4309.
10. E. Sagi. *Preferred frame parameters in the tensor-vector-scalar theory of gravity and its generalization.* Phys. Rev. D 80 (2009) 044032. arXiv:0905.4001.
11. J. W. Moffat, V. T. Toth. *The modified gravity (MOG) theory and its cosmology.* arXiv:0905.2226 (reply to the Deng–Xie–Huang comment).
12. X. Deng, Y. Xie, C.-G. Huang. *Comment on 'Modified scalar-tensor-vector gravity theory and the constraint on its parameters'.* arXiv:0905.0225.
13. C. Skordis, T. Złośnik. *Can TeVeS be a viable theory of gravity?* arXiv:1402.4696.
14. M. D. Seifert. *Stability of spherically symmetric spacetimes in metric $f(R)$ gravity and TeVeS.* Phys. Rev. D 76 (2007) 064002. arXiv:gr-qc/0703060.
15. C. R. Contaldi, T. Wiseman, B. Withers. *TeVeS gets caught on caustics.* Phys. Rev. D 78 (2008) 044034. arXiv:0802.1215.
