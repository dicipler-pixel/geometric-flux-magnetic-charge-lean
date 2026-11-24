import Mathlib

/-!
# `FluxCharge.TwoLevelWall` — what the non-Hermitian two-level wall actually says

The manuscript's model is `H(gamma) = sigma_x + i gamma sigma_z`, with `H(gamma)^2 = (1 - gamma^2) 1`.
The tempting sentence "for `gamma != 1` the formal projectors `(1/2)(1 +- H/sqrt(1-gamma^2))` are
idempotent" is FALSE, and this module proves it false: with `Real.sqrt` the scalar is `0` for
`|gamma| >= 1`, both projectors collapse to `(1/2) 1`, and they are not idempotent. The theorem is
repaired on `|gamma| < 1`, where the square root is real and positive; at `gamma = 1` the matrix is
a nonzero nilpotent and no orthogonal idempotent resolution exists at all.

Imports Mathlib only; nothing here depends on the monopole chain.
-/

open Matrix

namespace TwoLevelWall

/-- The non-Hermitian two-level Hamiltonian `σx + iγσz`. -/
noncomputable def H (g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) +
    (Complex.I * (g : ℂ)) • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)

/-- The `+` spectral-projector formula from the manuscript. -/
noncomputable def Pplus (g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + ((Real.sqrt (1 - g ^ 2) : ℝ) : ℂ)⁻¹ • H g)

/-- The `-` spectral-projector formula from the manuscript. -/
noncomputable def Pminus (g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 - ((Real.sqrt (1 - g ^ 2) : ℝ) : ℂ)⁻¹ • H g)

/-- A general square-root spectral-projector calculation. -/
theorem half_add_idempotent {A : Matrix (Fin 2) (Fin 2) ℂ} {c a : ℂ}
    (hA : A * A = a • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (hc : c * c * a = 1) :
    ((1 / 2 : ℂ) • (1 + c • A)) * ((1 / 2 : ℂ) • (1 + c • A)) =
      (1 / 2 : ℂ) • (1 + c • A) := by
  rw [smul_mul_smul_comm]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hA, smul_smul]
  rw [show c * c * a = 1 from hc]
  module

/-- The minus sign has the same abstract idempotence calculation. -/
theorem half_sub_idempotent {A : Matrix (Fin 2) (Fin 2) ℂ} {c a : ℂ}
    (hA : A * A = a • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (hc : c * c * a = 1) :
    ((1 / 2 : ℂ) • (1 - c • A)) * ((1 / 2 : ℂ) • (1 - c • A)) =
      (1 / 2 : ℂ) • (1 - c • A) := by
  have hc' : (-c) * (-c) * a = 1 := by
    calc
      (-c) * (-c) * a = c * c * a := by ring
      _ = 1 := hc
  simpa only [neg_smul, sub_eq_add_neg] using
    (half_add_idempotent (A := A) (c := -c) (a := a) hA hc')

/-- At `g = 2`, although `g ≠ 1`, the stated `+` projector is not idempotent. -/
theorem Pplus_two_not_idempotent : Pplus 2 * Pplus 2 ≠ Pplus 2 := by
  have hs : Real.sqrt (1 - (2 : ℝ) ^ 2) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (by norm_num)
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [Pplus, H, hs, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The square of the two-level Hamiltonian. -/
theorem H_sq (g : ℝ) :
    H g * H g = (1 - (g : ℂ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-- The characteristic determinant, valid for every real `γ`. -/
theorem H_sub_smul_det (g : ℝ) (lam : ℂ) :
    (H g - lam • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det =
      lam ^ 2 - (1 - (g : ℂ) ^ 2) := by
  rw [Matrix.det_fin_two]
  norm_num [H, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The characteristic equation of the two eigenvalues. -/
theorem H_eigenvalue_iff (g : ℝ) (lam : ℂ) :
    (H g - lam • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 ↔
      lam ^ 2 = 1 - (g : ℂ) ^ 2 := by
  simp only [H_sub_smul_det, sub_eq_zero]

/-- The exceptional Hamiltonian is nonzero. -/
theorem H_one_ne_zero : H 1 ≠ 0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [H] at h01

/-- At `γ = 1` the nonzero Hamiltonian is a Jordan wall. -/
theorem H_one_nilpotent : H 1 * H 1 = 0 := by
  rw [H_sq]
  norm_num

/-- The sum identity itself is valid for every real parameter. -/
theorem projectors_add (g : ℝ) : Pplus g + Pminus g = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pplus, Pminus] <;> ring

/-- Square-root degeneration outside the open unit interval. -/
theorem sqrt_unit_degenerate {g : ℝ} (hg : 1 ≤ |g|) :
    Real.sqrt (1 - g ^ 2) = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos
  nlinarith [sq_abs g, sq_nonneg g]

/-- On the degenerate domain both formal projectors collapse to half the identity. -/
theorem Pplus_of_unit_degenerate {g : ℝ} (hg : 1 ≤ |g|) :
    Pplus g = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Pplus, sqrt_unit_degenerate hg]
  norm_num

/-- On the degenerate domain the `+` formula is not idempotent. -/
theorem Pplus_not_idempotent_of_unit_degenerate {g : ℝ} (hg : 1 ≤ |g|) :
    Pplus g * Pplus g ≠ Pplus g := by
  rw [Pplus_of_unit_degenerate hg]
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- In particular, the theorem requested with only `g ≠ 1` is false. -/
theorem projectors_idempotent_not_forall_ne_one :
    ¬ (∀ g : ℝ, g ≠ 1 → Pplus g * Pplus g = Pplus g) := by
  intro h
  exact Pplus_two_not_idempotent (h 2 (by norm_num))

/-- The square-root scalar is nonzero and squares to the eigenvalue on `|g| < 1`. -/
theorem unit_radical_pos {g : ℝ} (hg : |g| < 1) : 0 < 1 - g ^ 2 := by
  have hg' := abs_lt.1 hg
  nlinarith

theorem sqrt_unit_pos {g : ℝ} (hg : |g| < 1) : 0 < Real.sqrt (1 - g ^ 2) :=
  Real.sqrt_pos.2 (unit_radical_pos hg)

theorem sqrt_unit_sq_complex {g : ℝ} (hg : |g| < 1) :
    (((Real.sqrt (1 - g ^ 2) : ℝ) : ℂ)) ^ 2 = 1 - (g : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (unit_radical_pos hg).le]
  push_cast
  ring

/-- On the valid domain the two eigenvalues are exactly `± sqrt (1 - γ²)`. -/
theorem H_eigenvalues_pm {g : ℝ} (hg : |g| < 1) :
    {lam : ℂ | (H g - lam • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0} =
      {(((Real.sqrt (1 - g ^ 2) : ℝ) : ℂ)),
        -(((Real.sqrt (1 - g ^ 2) : ℝ) : ℂ))} := by
  ext lam
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [H_eigenvalue_iff, ← sqrt_unit_sq_complex hg, sq_eq_sq_iff_eq_or_eq_neg]

/-- Corrected `+` projector theorem: the real-square-root formula needs `|g| < 1`. -/
theorem Pplus_idempotent {g : ℝ} (hg : |g| < 1) :
    Pplus g * Pplus g = Pplus g := by
  rw [Pplus]
  apply half_add_idempotent (H_sq g)
  rw [← sqrt_unit_sq_complex hg]
  have hq : (((Real.sqrt (1 - g ^ 2) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sqrt_unit_pos hg))
  field_simp

/-- Corrected `-` projector theorem on the same valid domain. -/
theorem Pminus_idempotent {g : ℝ} (hg : |g| < 1) :
    Pminus g * Pminus g = Pminus g := by
  rw [Pminus]
  apply half_sub_idempotent (H_sq g)
  rw [← sqrt_unit_sq_complex hg]
  have hq : (((Real.sqrt (1 - g ^ 2) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sqrt_unit_pos hg))
  field_simp

/-- At `γ = 1` the scalar in the manuscript's projector formula is zero. -/
theorem sqrt_at_one : Real.sqrt (1 - (1 : ℝ) ^ 2) = 0 := by
  norm_num

/-- Neither formal projector is idempotent at the exceptional point `γ = 1`. -/
theorem Pplus_one_not_idempotent : Pplus 1 * Pplus 1 ≠ Pplus 1 :=
  Pplus_not_idempotent_of_unit_degenerate (by norm_num)

/-- The `-` formula also collapses on the degenerate domain. -/
theorem Pminus_of_unit_degenerate {g : ℝ} (hg : 1 ≤ |g|) :
    Pminus g = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Pminus, sqrt_unit_degenerate hg]
  norm_num

/-- The `-` formula is not idempotent on the degenerate domain. -/
theorem Pminus_not_idempotent_of_unit_degenerate {g : ℝ} (hg : 1 ≤ |g|) :
    Pminus g * Pminus g ≠ Pminus g := by
  rw [Pminus_of_unit_degenerate hg]
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem Pminus_one_not_idempotent : Pminus 1 * Pminus 1 ≠ Pminus 1 :=
  Pminus_not_idempotent_of_unit_degenerate (by norm_num)

/-- An idempotent resolution `A = P-Q` gives an involution, not a nilpotent. -/
theorem sq_eq_one_of_idempotent_resolution
    {A P Q : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A = P - Q) (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hsum : P + Q = 1) : A * A = 1 := by
  have hQeq : Q = 1 - P := by
    rw [← hsum]
    abel
  have hQP : Q * P = 0 := by
    rw [hQeq, sub_mul, one_mul, hP, sub_self]
  calc
    A * A = P * P - P * Q - Q * P + Q * Q := by
      rw [hA]
      noncomm_ring
    _ = P + Q := by rw [hP, hQ, hPQ, hQP]; simp
    _ = 1 := hsum

/-- No orthogonal idempotent resolution `H 1 = P-Q`, `P+Q=1` exists. -/
theorem H_one_no_idempotent_resolution :
    ¬ ∃ P Q : Matrix (Fin 2) (Fin 2) ℂ,
      H 1 = P - Q ∧ P * P = P ∧ Q * Q = Q ∧ P * Q = 0 ∧ P + Q = 1 := by
  rintro ⟨P, Q, hA, hP, hQ, hPQ, hsum⟩
  have hs := sq_eq_one_of_idempotent_resolution hA hP hQ hPQ hsum
  have hzero : (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [← H_one_nilpotent]
    exact hs
  exact zero_ne_one hzero

end TwoLevelWall
