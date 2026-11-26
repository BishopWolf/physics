/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Dirac counting for the STVG and TeVeS field content

## i. Overview

Dirac's formula gives the number of degrees of freedom of a constrained
Hamiltonian system as `(2N - 2N1 - N2) / 2`, where `N` counts the canonical
fields and `N1`, `N2` the first- and second-class constraints.  This module
states the formula and applies it to the field content of the alternatives: a
Proca vector (four components, two second-class constraints), a unit timelike
vector (four components, one first-class constraint), a real scalar and the two
metric modes.

The constraint classification is input data, not derived here: the Poisson
brackets that make the Proca constraints second-class, and those that make the
unit-vector constraint first-class, are not computed.  What is formalised is
the counting formula applied to that classification.

## ii. Key results

- `DiracCount` and `DiracCount.dof` : the counting formula.
- `procaCount_dof`, `unitVectorCount_dof`, `realScalarCount_dof`,
  `gravitonCount_dof` : `3`, `3`, `1` and `2` degrees of freedom.
- `stvgCount_dof`, `tevesCount_dof` : `6` for both, with the sums made explicit.

## iii. Table of contents

- A. The counting formula
- B. Applications

## iv. References

* P. A. M. Dirac, *Lectures on Quantum Mechanics*, Yeshiva University, 1964.
* M. Henneaux, C. Teitelboim, *Quantization of Gauge Systems*, Princeton, 1992.
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. The counting formula -/

/-- A field content counted the Dirac way: canonical fields and the numbers of
first- and second-class constraints. -/
structure DiracCount where
  /-- Number of canonical field components. -/
  components : ℕ
  /-- Number of first-class constraints. -/
  firstClass : ℕ
  /-- Number of second-class constraints. -/
  secondClass : ℕ

/-- Dirac's formula `(2N - 2N1 - N2) / 2` for the number of degrees of
freedom.  The subtraction is truncated natural-number subtraction; all the
instances below have `2N >= 2N1 + N2`. -/
def DiracCount.dof (D : DiracCount) : ℕ :=
  (2 * D.components - 2 * D.firstClass - D.secondClass) / 2

/-! ## B. Applications -/

/-- A massive Proca vector: four components, two second-class constraints. -/
def procaCount : DiracCount := ⟨4, 0, 2⟩

/-- The Proca field has three degrees of freedom. -/
theorem procaCount_dof : procaCount.dof = 3 := by decide

/-- A unit timelike vector: four components, one first-class constraint. -/
def unitVectorCount : DiracCount := ⟨4, 1, 0⟩

/-- The unit timelike vector has three degrees of freedom. -/
theorem unitVectorCount_dof : unitVectorCount.dof = 3 := by decide

/-- A real scalar field: one component, no constraints. -/
def realScalarCount : DiracCount := ⟨1, 0, 0⟩

/-- The real scalar has one degree of freedom. -/
theorem realScalarCount_dof : realScalarCount.dof = 1 := by decide

/-- The two metric modes: two components, no constraints. -/
def gravitonCount : DiracCount := ⟨2, 0, 0⟩

/-- The metric contributes two degrees of freedom. -/
theorem gravitonCount_dof : gravitonCount.dof = 2 := by decide

/-- STVG: two metric modes, a Proca vector and one scalar. -/
def stvgCount : DiracCount := ⟨7, 0, 2⟩

/-- STVG has six degrees of freedom. -/
theorem stvgCount_dof : stvgCount.dof = 6 := by decide

/-- The STVG count is the sum of its sectors. -/
theorem stvgCount_dof_eq_sum :
    stvgCount.dof = gravitonCount.dof + procaCount.dof + realScalarCount.dof := by
  decide

/-- TeVeS: two metric modes, a unit timelike vector and one scalar. -/
def tevesCount : DiracCount := ⟨7, 1, 0⟩

/-- TeVeS has six degrees of freedom. -/
theorem tevesCount_dof : tevesCount.dof = 6 := by decide

/-- The TeVeS count is the sum of its sectors. -/
theorem tevesCount_dof_eq_sum :
    tevesCount.dof = gravitonCount.dof + unitVectorCount.dof + realScalarCount.dof := by
  decide

end GeneralRelativity
