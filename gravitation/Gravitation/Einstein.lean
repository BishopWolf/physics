import Gravitation.Curvature

/-!
# The Einstein tensor and the vacuum equations

`G_{ij} = Ric_{ij} - (1/2) S g_{ij}`, with `Ric` contracted against the inverse
metric.

Main results:

* `einstein_symm` : `G` is symmetric.
* `metricTrace_einstein` : `g^{ij} G_{ij} = (1 - n/2) S`, so in four dimensions
  the trace of `G` is `-S` (the Einstein tensor is *not* trace free).
* `vacuum_iff_ricci_flat` : in four dimensions `G = 0 ↔ Ric = 0`.
-/

namespace Gravitation

variable {n : ℕ}

/-- Full contraction of the inverse metric with a rank-2 tensor, `g^{ij} T_{ij}`. -/
def metricTrace (M : Metric n) (T : Tensor2 n) : ℝ := ∑ i, ∑ j, M.ginv i j * T i j

/-- The Einstein tensor `G_{ij} = Ric_{ij} - (1/2) S g_{ij}`. -/
noncomputable def einstein (M : Metric n) (R : Riemann n) : Tensor2 n :=
  fun i j => ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j

theorem scalarCurv_eq_metricTrace (M : Metric n) (R : Riemann n) :
    scalarCurv M R = metricTrace M (ricci M R) := rfl

/-- The Einstein tensor is symmetric. -/
theorem einstein_symm (M : Metric n) (R : Riemann n) : IsSymm (einstein M R) := by
  intro i j
  simp only [einstein]
  rw [ricci_symm M R i j, M.symm i j]

/-- `∑_{ij} g^{ij} g_{ij} = n`, i.e. the trace of `g^{-1} g` is the dimension. -/
theorem sum_ginv_mul_g (M : Metric n) :
    (∑ i, ∑ j, M.ginv i j * M.g i j) = (n : ℝ) := by
  have h1 : ∀ i, (∑ j, M.ginv i j * M.g i j) = (M.ginv * M.g) i i := by
    intro i
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [M.symm j i])
  calc (∑ i, ∑ j, M.ginv i j * M.g i j)
      = ∑ i, (M.ginv * M.g) i i := Finset.sum_congr rfl (fun i _ => h1 i)
    _ = ∑ i, (1 : Tensor2 n) i i := by rw [M.inv_right]
    _ = (n : ℝ) := by simp

/-- Metric trace of the Einstein tensor: `g^{ij} G_{ij} = (1 - n/2) S`. -/
theorem metricTrace_einstein (M : Metric n) (R : Riemann n) :
    metricTrace M (einstein M R) = (1 - (n : ℝ) / 2) * scalarCurv M R := by
  have hsplit : ∀ i,
      (∑ j, M.ginv i j * (ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j))
        = (∑ j, M.ginv i j * ricci M R i j)
          - (1 / 2) * scalarCurv M R * (∑ j, M.ginv i j * M.g i j) := by
    intro i
    have hterm : ∀ j,
        M.ginv i j * (ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j)
          = M.ginv i j * ricci M R i j
            - (1 / 2) * scalarCurv M R * (M.ginv i j * M.g i j) := by
      intro j
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
      ← Finset.mul_sum]
  simp only [metricTrace, einstein]
  calc (∑ i, ∑ j, M.ginv i j * (ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j))
      = ∑ i, ((∑ j, M.ginv i j * ricci M R i j)
          - (1 / 2) * scalarCurv M R * (∑ j, M.ginv i j * M.g i j)) :=
        Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = (∑ i, ∑ j, M.ginv i j * ricci M R i j)
          - (1 / 2) * scalarCurv M R * (∑ i, ∑ j, M.ginv i j * M.g i j) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = scalarCurv M R - (1 / 2) * scalarCurv M R * (n : ℝ) := by
        rw [sum_ginv_mul_g]
        rfl
    _ = (1 - (n : ℝ) / 2) * scalarCurv M R := by ring

/-- In four dimensions, `G = 0` forces the scalar curvature to vanish. -/
theorem scalarCurv_eq_zero_of_einstein_eq_zero (M : Metric 4) (R : Riemann 4)
    (h : einstein M R = 0) : scalarCurv M R = 0 := by
  have htr : metricTrace M (einstein M R) = 0 := by
    rw [h]
    simp [metricTrace]
  rw [metricTrace_einstein] at htr
  norm_num at htr
  linarith

/-- In four dimensions the vacuum Einstein equation `G = 0` is equivalent to
Ricci flatness. -/
theorem vacuum_iff_ricci_flat (M : Metric 4) (R : Riemann 4) :
    einstein M R = 0 ↔ ricci M R = 0 := by
  constructor
  · intro h
    have hS := scalarCurv_eq_zero_of_einstein_eq_zero M R h
    ext i j
    have hij : ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j = 0 := by
      have hc := congrFun (congrFun h i) j
      simpa [einstein] using hc
    rw [hS] at hij
    simpa using hij
  · intro h
    ext i j
    have hS : scalarCurv M R = 0 := by simp [scalarCurv, h]
    simp [einstein, h, hS]

end Gravitation
