import Mathlib

open scoped Matrix Complex Topology BigOperators
open Filter Set

namespace SpectralWall

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable section

/-- The Schwarzschild effective potential.  The second argument is the
square of angular momentum and is held fixed in `V_r` and `V_rr`. -/
def V (r Lam : ℝ) : ℝ := (1 - 2 / r) * (1 + Lam / r ^ 2)

def circular (r : ℝ) : ℝ := r ^ 2 / (r - 3)

def W (r : ℝ) : ℝ := (r - 6) / (r ^ 3 * (r - 3))

def M (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -W r, 0]

def H (g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0] + (Complex.I * (g : ℂ)) • !![1, 0; 0, -1]

private lemma hasDerivAt_id_pow_two (r : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
  convert (hasDerivAt_id r).pow 2 using 1 <;> try rfl
  norm_num

private lemma hasDerivAt_id_pow_three (r : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 3) (3 * r ^ 2) r := by
  convert (hasDerivAt_id r).pow 3 using 1 <;> try rfl
  norm_num

private lemma hasDerivAt_id_pow_four (r : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 4) (4 * r ^ 3) r := by
  convert (hasDerivAt_id r).pow 4 using 1 <;> try rfl
  norm_num

private lemma hasDerivAt_const_div_sq (a r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => a / s ^ 2) (-(2 * a) / r ^ 3) r := by
  convert (hasDerivAt_const r a).div (hasDerivAt_id_pow_two r)
    (pow_ne_zero 2 hr) using 1
  field_simp
  ring

private lemma hasDerivAt_const_div_cube (a r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => a / s ^ 3) (-(3 * a) / r ^ 4) r := by
  convert (hasDerivAt_const r a).div (hasDerivAt_id_pow_three r)
    (pow_ne_zero 3 hr) using 1
  field_simp
  ring

private lemma hasDerivAt_const_div_fourth (a r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => a / s ^ 4) (-(4 * a) / r ^ 5) r := by
  convert (hasDerivAt_const r a).div (hasDerivAt_id_pow_four r)
    (pow_ne_zero 4 hr) using 1
  field_simp
  ring

/-- First radial partial derivative, with `Lam` fixed. -/
theorem hasDerivAt_V_r (Lam r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s => V s Lam)
      (2 / r ^ 2 - 2 * Lam / r ^ 3 + 6 * Lam / r ^ 4) r := by
  have h0 : HasDerivAt (fun s : ℝ => 1 - 2 / s) (2 / r ^ 2) r := by
    convert (hasDerivAt_const r (1 : ℝ)).sub
      ((hasDerivAt_const r (2 : ℝ)).div (hasDerivAt_id r) hr) using 1
    · rfl
    · simp only [id_eq]
      field_simp [hr]
      ring
  have hL : HasDerivAt (fun s : ℝ => Lam / s ^ 2) (-(2 * Lam) / r ^ 3) r :=
    hasDerivAt_const_div_sq Lam r hr
  have h1 : HasDerivAt (fun s : ℝ => 1 + Lam / s ^ 2)
      (-(2 * Lam) / r ^ 3) r := by
    convert (hasDerivAt_const r (1 : ℝ)).add hL using 1 <;> ring
  convert h0.mul h1 using 1
  · rfl
  · field_simp
    ring

/-- The second radial partial derivative is taken before specializing `Lam`. -/
theorem hasDerivAt_V_rr (Lam r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s => deriv (fun q => V q Lam) s)
      (6 * Lam / r ^ 4 - 24 * Lam / r ^ 5 - 4 / r ^ 3) r := by
  have h2 := hasDerivAt_const_div_sq 2 r hr
  have h3 := hasDerivAt_const_div_cube (2 * Lam) r hr
  have h4 := hasDerivAt_const_div_fourth (6 * Lam) r hr
  have h : HasDerivAt (fun s : ℝ => 2 / s ^ 2 - 2 * Lam / s ^ 3 + 6 * Lam / s ^ 4)
      (6 * Lam / r ^ 4 - 24 * Lam / r ^ 5 - 4 / r ^ 3) r := by
    convert (h2.sub h3).add h4 using 1
    field_simp
    ring
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hr] with s hs
  exact (hasDerivAt_V_r Lam s hs).deriv

theorem deriv_V_r (Lam r : ℝ) (hr : r ≠ 0) :
    deriv (fun s => V s Lam) r =
      2 / r ^ 2 - 2 * Lam / r ^ 3 + 6 * Lam / r ^ 4 :=
  (hasDerivAt_V_r Lam r hr).deriv

theorem deriv_V_rr (Lam r : ℝ) (hr : r ≠ 0) :
    deriv (fun s => deriv (fun q => V q Lam) s) r =
      6 * Lam / r ^ 4 - 24 * Lam / r ^ 5 - 4 / r ^ 3 :=
  (hasDerivAt_V_rr Lam r hr).deriv

/-- Equation (40): substitution is made only after taking two radial derivatives. -/
theorem deriv_V_rr_circular (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3) :
    deriv (fun s => deriv (fun q => V q (circular r)) s) r = 2 * W r := by
  rw [deriv_V_rr _ _ hr]
  simp only [circular, W]
  field_simp [hr, hr3]
  ring

theorem half_deriv_V_rr_circular (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3) :
    (1 / 2 : ℝ) * deriv (fun s => deriv (fun q => V q (circular r)) s) r = W r := by
  rw [deriv_V_rr_circular r hr hr3]
  ring

theorem M_sq (r : ℝ) : M r * M r = (-(W r)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem M_sq_eq_zero_iff (r : ℝ) : M r * M r = 0 ↔ W r = 0 := by
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simpa [M, Matrix.mul_apply, Fin.sum_univ_two] using h00.symm
  · intro h
    rw [M_sq, h]
    simp

theorem M_ne_zero (r : ℝ) : M r ≠ 0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [M] at h01

theorem M_six_ne_zero : M 6 ≠ 0 := M_ne_zero 6

theorem W_six : W 6 = 0 := by norm_num [W]

theorem M_six_sq : M 6 * M 6 = 0 := (M_sq_eq_zero_iff 6).2 W_six

theorem W_eq_zero_iff_of_three_lt {r : ℝ} (hr : 3 < r) : W r = 0 ↔ r = 6 := by
  have hr0 : r ≠ 0 := by linarith
  have hr3 : r - 3 ≠ 0 := by linarith
  have hd : r ^ 3 * (r - 3) ≠ 0 := mul_ne_zero (pow_ne_zero 3 hr0) hr3
  constructor
  · intro h
    rcases (div_eq_zero_iff).1 h with hnum | hden
    · linarith
    · exact (hd hden).elim
  · rintro rfl
    exact W_six

theorem W_pos_iff_of_three_lt {r : ℝ} (hr : 3 < r) : 0 < W r ↔ 6 < r := by
  have hd : 0 < r ^ 3 * (r - 3) := by positivity
  rw [W, div_pos_iff]
  constructor
  · rintro (⟨hn, _⟩ | ⟨hn, hdn⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨by linarith, hd⟩

theorem W_neg_iff_of_three_lt {r : ℝ} (hr : 3 < r) : W r < 0 ↔ r < 6 := by
  have hd : 0 < r ^ 3 * (r - 3) := by positivity
  rw [W, div_neg_iff]
  constructor
  · rintro (⟨hn, _⟩ | ⟨hn, hdn⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hd⟩

theorem M_sub_smul_one_det (r lam : ℝ) :
    (M r - lam • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = lam ^ 2 + W r := by
  simp [M, Matrix.det_fin_two, Matrix.sub_apply, Matrix.one_apply]
  ring

/-- The real matrix viewed as a complex matrix. -/
def MC (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (M r).map (fun x : ℝ => (x : ℂ))

theorem MC_mulVec_eigen_iff (r : ℝ) (lam : ℂ) :
    MC r *ᵥ ![1, lam] = lam • ![1, lam] ↔ lam ^ 2 = -(W r : ℂ) := by
  constructor
  · intro h
    have h1 := congr_fun h 1
    simp [MC, M, Matrix.mulVec_fin_two] at h1
    linear_combination -h1
  · intro h
    funext i
    fin_cases i
    · simp [MC, M, Matrix.mulVec_fin_two]
    · simp [MC, M, Matrix.mulVec_fin_two]
      linear_combination -h

theorem M_mulVec_eigen_real_iff (r lam : ℝ) :
    M r *ᵥ ![1, lam] = lam • ![1, lam] ↔ lam ^ 2 = -W r := by
  constructor
  · intro h
    have h1 := congr_fun h 1
    simp [M, Matrix.mulVec_fin_two] at h1
    linear_combination -h1
  · intro h
    funext i
    fin_cases i
    · simp [M, Matrix.mulVec_fin_two]
    · simp [M, Matrix.mulVec_fin_two]
      linear_combination -h

private lemma I_mul_sqrt_sq {x : ℝ} (hx : 0 ≤ x) :
    (Complex.I * (Real.sqrt x : ℂ)) ^ 2 = -(x : ℂ) := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hx]
  push_cast
  ring

/-- The upper/lower oscillatory eigenvectors outside the wall. -/
theorem oscillation_eigenvectors {r : ℝ} (hr : 6 < r) :
    MC r *ᵥ ![1, Complex.I * (Real.sqrt (W r) : ℂ)] =
        (Complex.I * (Real.sqrt (W r) : ℂ)) •
          ![1, Complex.I * (Real.sqrt (W r) : ℂ)] ∧
    MC r *ᵥ ![1, -Complex.I * (Real.sqrt (W r) : ℂ)] =
        (-Complex.I * (Real.sqrt (W r) : ℂ)) •
          ![1, -Complex.I * (Real.sqrt (W r) : ℂ)] := by
  have hW : 0 < W r := (W_pos_iff_of_three_lt (by linarith)).2 hr
  constructor
  · apply (MC_mulVec_eigen_iff _ _).2
    exact I_mul_sqrt_sq hW.le
  · apply (MC_mulVec_eigen_iff _ _).2
    rw [show (-Complex.I * (Real.sqrt (W r) : ℂ)) ^ 2 =
      (Complex.I * (Real.sqrt (W r) : ℂ)) ^ 2 by ring]
    exact I_mul_sqrt_sq hW.le

theorem oscillation_eigenvalues_nonreal {r : ℝ} (hr : 6 < r) :
    (Complex.I * (Real.sqrt (W r) : ℂ)).im ≠ 0 ∧
    (-Complex.I * (Real.sqrt (W r) : ℂ)).im ≠ 0 := by
  have hW : 0 < W r := (W_pos_iff_of_three_lt (by linarith)).2 hr
  have hs : 0 < Real.sqrt (W r) := Real.sqrt_pos.2 hW
  simp only [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero,
    sub_zero, add_zero, ne_eq]
  constructor <;> linarith

/-- The two real eigenvectors in the growth regime. -/
theorem growth_eigenvectors {r : ℝ} (hr3 : 3 < r) (hr6 : r < 6) :
    M r *ᵥ ![1, Real.sqrt (-W r)] = (Real.sqrt (-W r)) • ![1, Real.sqrt (-W r)] ∧
    M r *ᵥ ![1, -Real.sqrt (-W r)] = (-Real.sqrt (-W r)) • ![1, -Real.sqrt (-W r)] := by
  have hW : W r < 0 := (W_neg_iff_of_three_lt hr3).2 hr6
  have hs : 0 ≤ -W r := by linarith
  constructor
  · exact (M_mulVec_eigen_real_iff _ _).2 (Real.sq_sqrt hs)
  · apply (M_mulVec_eigen_real_iff _ _).2
    rw [show (-Real.sqrt (-W r)) ^ 2 = (Real.sqrt (-W r)) ^ 2 by ring]
    exact Real.sq_sqrt hs

theorem growing_eigenvalue_pos {r : ℝ} (hr3 : 3 < r) (hr6 : r < 6) :
    0 < Real.sqrt (-W r) := by
  apply Real.sqrt_pos.2
  have := (W_neg_iff_of_three_lt hr3).2 hr6
  linarith

theorem growth_eigenvalues_nonzero {r : ℝ} (hr3 : 3 < r) (hr6 : r < 6) :
    Real.sqrt (-W r) ≠ 0 ∧ -Real.sqrt (-W r) ≠ 0 := by
  have h := growing_eigenvalue_pos hr3 hr6
  exact ⟨ne_of_gt h, neg_ne_zero.mpr (ne_of_gt h)⟩

theorem oscillation_gap {r : ℝ} (hr : 6 < r) :
    ‖Complex.I * (Real.sqrt (W r) : ℂ) -
      (-Complex.I * (Real.sqrt (W r) : ℂ))‖ = 2 * Real.sqrt |W r| := by
  have hW : 0 < W r := (W_pos_iff_of_three_lt (by linarith)).2 hr
  rw [show Complex.I * (Real.sqrt (W r) : ℂ) -
      (-Complex.I * (Real.sqrt (W r) : ℂ)) =
      (((2 * Real.sqrt (W r) : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (W r)), abs_of_pos hW]

theorem growth_gap {r : ℝ} (hr3 : 3 < r) (hr6 : r < 6) :
    |Real.sqrt (-W r) - (-Real.sqrt (-W r))| = 2 * Real.sqrt |W r| := by
  have hW : W r < 0 := (W_neg_iff_of_three_lt hr3).2 hr6
  rw [abs_of_neg hW]
  rw [show Real.sqrt (-W r) - (-Real.sqrt (-W r)) = 2 * Real.sqrt (-W r) by ring]
  exact abs_of_nonneg (by positivity)

/-- On the physical domain `r > 3`, the modulus of `W` has a simple zero at six. -/
theorem abs_W_div_abs_sub_six {r : ℝ} (hr3 : 3 < r) (hr6 : r ≠ 6) :
    |W r| / |r - 6| = 1 / (r ^ 3 * (r - 3)) := by
  have hd : 0 < r ^ 3 * (r - 3) := by positivity
  have ha : |r - 6| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hr6)
  rw [W, abs_div, abs_of_pos hd]
  field_simp [ha, ne_of_gt hd]

/-- The inverse-cube law for the paper's exponent `p`. -/
def p (r : ℝ) : ℝ := 2 + 6 / r

theorem p_six : p 6 = 3 := by norm_num [p]

theorem H_sq (g : ℝ) : H g * H g = (1 - (g : ℂ) ^ 2) •
    (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem H_one_ne_zero : H 1 ≠ 0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [H] at h01

theorem H_one_sq : H 1 * H 1 = 0 := by
  rw [H_sq]
  norm_num

/-- A spectral decomposition into two complementary orthogonal rank-one
projections would force `H 1` to square to the identity. -/
theorem H_one_no_idempotent_decomposition
    (P Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hdecomp : H 1 = P - Q) (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hsum : P + Q = 1) : False := by
  have hQeq : Q = 1 - P := by rw [← hsum]; abel
  have hQP : Q * P = 0 := by rw [hQeq, sub_mul, one_mul, hP, sub_self]
  have hsq : H 1 * H 1 = 1 := by
    rw [hdecomp]
    calc
      (P - Q) * (P - Q) = P * P + Q * Q := by
        rw [mul_sub, sub_mul, sub_mul, hPQ, hQP]
        simp only [mul_one, sub_zero, zero_sub, zero_add]
        abel
      _ = P + Q := by rw [hP, hQ]
      _ = 1 := hsum
  rw [H_one_sq] at hsq
  have h00 := congr_fun (congr_fun hsq 0) 0
  norm_num [Matrix.one_apply] at h00

/-- Positive spectral scale in the formal projectors. -/
def scale (g : ℝ) : ℂ := (Real.sqrt (1 - g ^ 2) : ℂ)

def Pplus (g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (scale g)⁻¹ • H g)

def Pminus (g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 - (scale g)⁻¹ • H g)

theorem scale_sq {g : ℝ} (hg : 0 ≤ 1 - g ^ 2) :
    (scale g) ^ 2 = (1 - (g : ℂ) ^ 2) := by
  rw [scale, ← Complex.ofReal_pow, Real.sq_sqrt hg]
  push_cast
  ring

theorem H_sq_scale {g : ℝ} (hg : 0 ≤ 1 - g ^ 2) :
    H g * H g = (scale g) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [H_sq, scale_sq hg]

theorem formal_projectors_sum (g : ℝ) : Pplus g + Pminus g = 1 := by
  simp only [Pplus, Pminus]
  module

theorem Pplus_idempotent {g : ℝ} (hg : 0 ≤ 1 - g ^ 2) (hc : scale g ≠ 0) :
    Pplus g * Pplus g = Pplus g := by
  have hic2 : (scale g)⁻¹ * (scale g)⁻¹ * (scale g) ^ 2 = 1 := by
    field_simp
  rw [Pplus, smul_mul_smul]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul,
    H_sq_scale hg, smul_add, smul_smul]
  rw [hic2]
  have hcinv2 : (1 / 2 : ℂ) * (1 / 2) = 1 / 4 := by norm_num
  rw [hcinv2]
  module

theorem Pminus_idempotent {g : ℝ} (hg : 0 ≤ 1 - g ^ 2) (hc : scale g ≠ 0) :
    Pminus g * Pminus g = Pminus g := by
  have hic2 : (scale g)⁻¹ * (scale g)⁻¹ * (scale g) ^ 2 = 1 := by
    field_simp
  rw [Pminus, smul_mul_smul]
  simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_smul,
    H_sq_scale hg, smul_sub, smul_smul]
  rw [hic2]
  have hcinv2 : (1 / 2 : ℂ) * (1 / 2) = 1 / 4 := by norm_num
  rw [hcinv2]
  module

/-- In particular, away from both wall parameters `g = ±1`, the formal
projectors sum to one and are idempotent. -/
theorem formal_projectors_of_ne {g : ℝ} (hg : 0 ≤ 1 - g ^ 2)
    (hg1 : g ≠ 1) (hgneg1 : g ≠ -1) :
    Pplus g + Pminus g = 1 ∧ Pplus g * Pplus g = Pplus g ∧
      Pminus g * Pminus g = Pminus g := by
  have hreal : Real.sqrt (1 - g ^ 2) ≠ 0 := by
    apply Real.sqrt_ne_zero'.2
    have h1 : g ^ 2 < 1 := by
      by_contra! h
      have hs : g ^ 2 = 1 := le_antisymm (by linarith [hg]) h
      have hz : (g - 1) * (g + 1) = 0 := by nlinarith [hs]
      rcases mul_eq_zero.mp hz with hz1 | hz2
      · exact hg1 (by linarith)
      · exact hgneg1 (by linarith)
    linarith
  have hc : scale g ≠ 0 := by
    simpa only [scale, ne_eq, Complex.ofReal_eq_zero] using hreal
  exact ⟨formal_projectors_sum g, Pplus_idempotent hg hc, Pminus_idempotent hg hc⟩

theorem formal_projectors_of_between {g : ℝ} (hgneg1 : -1 < g) (hg1 : g < 1) :
    Pplus g + Pminus g = 1 ∧ Pplus g * Pplus g = Pplus g ∧
      Pminus g * Pminus g = Pminus g := by
  have hp : 0 < (1 - g) * (g + 1) := mul_pos (by linarith) (by linarith)
  exact formal_projectors_of_ne (by nlinarith) (by linarith) (by linarith)

theorem scale_one : scale 1 = 0 := by norm_num [scale]

/-- The usual square-root eigenvalue equations away from the exceptional point. -/
theorem two_level_eigenvalue_squares {g : ℝ} (hg : 0 ≤ 1 - g ^ 2) :
    (scale g) ^ 2 = 1 - (g : ℂ) ^ 2 ∧ (-scale g) ^ 2 = 1 - (g : ℂ) ^ 2 := by
  exact ⟨scale_sq hg, by rw [neg_sq]; exact scale_sq hg⟩

theorem H_sub_smul_one_det (g : ℝ) (lam : ℂ) :
    (H g - lam • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det =
      lam ^ 2 - (1 - (g : ℂ) ^ 2) := by
  simp [H, Matrix.det_fin_two, Matrix.sub_apply, Matrix.one_apply]
  ring_nf
  simp [Complex.I_sq]

theorem two_level_eigenvalues_iff {g : ℝ} (hg : 0 ≤ 1 - g ^ 2) (lam : ℂ) :
    lam ^ 2 = 1 - (g : ℂ) ^ 2 ↔ lam = scale g ∨ lam = -scale g := by
  constructor
  · intro h
    have hfactor : (lam - scale g) * (lam + scale g) = 0 := by
      linear_combination h - scale_sq hg
    rcases mul_eq_zero.mp hfactor with hp | hm
    · exact Or.inl (sub_eq_zero.mp hp)
    · exact Or.inr (by linear_combination hm)
  · rintro (rfl | rfl)
    · exact scale_sq hg
    · rw [neg_sq]
      exact scale_sq hg

private lemma sqrt_gap_ratio_eq {r : ℝ} (hr3 : 3 < r) (hr6 : r ≠ 6) :
    2 * Real.sqrt |W r| / Real.sqrt |r - 6| =
      2 * Real.sqrt (1 / (r ^ 3 * (r - 3))) := by
  have hsqrt : Real.sqrt (|W r| / |r - 6|) =
      Real.sqrt |W r| / Real.sqrt |r - 6| :=
    Real.sqrt_div (abs_nonneg _) _
  calc
    2 * Real.sqrt |W r| / Real.sqrt |r - 6| =
        2 * (Real.sqrt |W r| / Real.sqrt |r - 6|) := by ring
    _ = 2 * Real.sqrt (|W r| / |r - 6|) := by rw [hsqrt]
    _ = 2 * Real.sqrt (1 / (r ^ 3 * (r - 3))) := by
      rw [abs_W_div_abs_sub_six hr3 hr6]

private lemma tendsto_continuous_gap_factor :
    Tendsto (fun r : ℝ => 2 * Real.sqrt (1 / (r ^ 3 * (r - 3))))
      (nhdsWithin 6 (Ioi 6)) (nhds (2 / Real.sqrt 648)) := by
  have hcont : ContinuousAt (fun r : ℝ => 2 * Real.sqrt (1 / (r ^ 3 * (r - 3)))) 6 := by
    fun_prop (disch := norm_num)
  have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds : nhdsWithin (6 : ℝ) (Ioi 6) ≤ nhds 6)
  convert h using 1 <;> norm_num [Real.sqrt_div, div_eq_mul_inv]

/-- The square-root gap law from above the ISCO. -/
theorem tendsto_gap_sqrt_from_above :
    Tendsto (fun r : ℝ => 2 * Real.sqrt |W r| / Real.sqrt |r - 6|)
      (nhdsWithin 6 (Ioi 6)) (nhds (2 / Real.sqrt 648)) := by
  apply tendsto_continuous_gap_factor.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 6 < r at hr
  exact (sqrt_gap_ratio_eq (by linarith) (by linarith)).symm

/-- The same square-root gap law from below the ISCO. -/
theorem tendsto_gap_sqrt_from_below :
    Tendsto (fun r : ℝ => 2 * Real.sqrt |W r| / Real.sqrt |r - 6|)
      (nhdsWithin 6 (Iio 6)) (nhds (2 / Real.sqrt 648)) := by
  have hcont : ContinuousAt (fun r : ℝ => 2 * Real.sqrt (1 / (r ^ 3 * (r - 3)))) 6 := by
    fun_prop (disch := norm_num)
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds : nhdsWithin (6 : ℝ) (Iio 6) ≤ nhds 6)
  have htarget : 2 * Real.sqrt (1 / ((6 : ℝ) ^ 3 * (6 - 3))) = 2 / Real.sqrt 648 := by
    norm_num [Real.sqrt_div, div_eq_mul_inv]
  rw [← htarget]
  apply hlim.congr'
  have h3 : ∀ᶠ r : ℝ in nhdsWithin 6 (Iio 6), 3 < r :=
    Filter.Eventually.filter_mono
      (show nhdsWithin (6 : ℝ) (Iio 6) ≤ nhds 6 from nhdsWithin_le_nhds)
      (eventually_gt_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, h3] with r hr hr3
  change r < 6 at hr
  exact (sqrt_gap_ratio_eq hr3 (by linarith)).symm

/-- The derivative of `W`, kept in its unevaluated rational form so that its
continuity at `r = 6` is immediate. -/
def DW (r : ℝ) : ℝ :=
  (r ^ 3 * (r - 3) - (r - 6) * (3 * r ^ 2 * (r - 3) + r ^ 3)) /
    (r ^ 3 * (r - 3)) ^ 2

theorem hasDerivAt_W (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3) :
    HasDerivAt W (DW r) r := by
  have hden : HasDerivAt (fun s : ℝ => s ^ 3 * (s - 3))
      (3 * r ^ 2 * (r - 3) + r ^ 3) r := by
    convert (hasDerivAt_id_pow_three r).mul ((hasDerivAt_id r).sub_const 3) using 1
    · rfl
    · simp only [id_eq]
      ring
  convert ((hasDerivAt_id r).sub_const 6).div hden
    (mul_ne_zero (pow_ne_zero 3 hr) (sub_ne_zero.mpr hr3)) using 1
  · rfl
  · simp only [DW, id_eq, one_mul, mul_one]

theorem hasDerivAt_growingEigenvalue (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3)
    (hW : W r ≠ 0) :
    HasDerivAt (fun s => Real.sqrt (-W s)) (-DW r / (2 * Real.sqrt (-W r))) r := by
  have hneg : HasDerivAt (fun s => -W s) (-DW r) r := by
    convert (hasDerivAt_W r hr hr3).neg using 1 <;> rfl
  have hn : -W r ≠ 0 := neg_ne_zero.mpr hW
  convert (Real.hasDerivAt_sqrt hn).comp r hneg using 1
  · rfl
  · ring

theorem deriv_growingEigenvalue (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3)
    (hW : W r ≠ 0) :
    deriv (fun s => Real.sqrt (-W s)) r = -DW r / (2 * Real.sqrt (-W r)) :=
  (hasDerivAt_growingEigenvalue r hr hr3 hW).deriv

/-- The growing eigenvector on the inside of the wall. -/
def growingEigenvector (r : ℝ) : Fin 2 → ℝ := ![1, Real.sqrt (-W r)]

theorem growingEigenvector_eigen {r : ℝ} (hr3 : 3 < r) (hr6 : r < 6) :
    M r *ᵥ growingEigenvector r = Real.sqrt (-W r) • growingEigenvector r ∧
      0 < Real.sqrt (-W r) := by
  exact ⟨(growth_eigenvectors hr3 hr6).1, growing_eigenvalue_pos hr3 hr6⟩

theorem DW_six : DW 6 = 1 / 648 := by norm_num [DW]

/-- The derivative of the growing eigenvalue diverges to `atBot` from inside
the wall. -/
theorem tendsto_deriv_growingEigenvalue_from_below :
    Tendsto (fun r => deriv (fun s => Real.sqrt (-W s)) r)
      (nhdsWithin 6 (Iio 6)) atBot := by
  let l := nhdsWithin (6 : ℝ) (Iio 6)
  have h3 : ∀ᶠ r : ℝ in l, 3 < r :=
    Filter.Eventually.filter_mono
      (show l ≤ nhds 6 from nhdsWithin_le_nhds)
      (eventually_gt_nhds (by norm_num))
  have hbelow : ∀ᶠ r : ℝ in l, r < 6 := self_mem_nhdsWithin
  have hnum : Tendsto (fun r => -DW r) l (nhds (-(1 / 648) : ℝ)) := by
    have hc : ContinuousAt DW 6 := by
      unfold DW
      fun_prop (disch := norm_num)
    have h := hc.tendsto.mono_left (show l ≤ nhds 6 from nhdsWithin_le_nhds)
    have hn := h.neg
    rw [DW_six] at hn
    exact hn
  have hden0 : Tendsto (fun r => 2 * Real.sqrt (-W r)) l (nhds 0) := by
    have hc : ContinuousAt (fun r : ℝ => 2 * Real.sqrt (-W r)) 6 := by
      simp only [W]
      fun_prop (disch := norm_num)
    have h := hc.tendsto.mono_left (show l ≤ nhds 6 from nhdsWithin_le_nhds)
    convert h using 1 <;> norm_num [W]
  have hdenpos : ∀ᶠ r : ℝ in l, 0 < 2 * Real.sqrt (-W r) := by
    filter_upwards [h3, hbelow] with r hr3 hr6
    have hs := growing_eigenvalue_pos hr3 hr6
    positivity
  have hdenGT : Tendsto (fun r => 2 * Real.sqrt (-W r)) l (nhdsWithin 0 (Ioi 0)) := by
    exact tendsto_nhdsWithin_iff.2 ⟨hden0, hdenpos⟩
  have hinv : Tendsto (fun r => (2 * Real.sqrt (-W r))⁻¹) l atTop :=
    hdenGT.inv_tendsto_nhdsGT_zero
  have hquot : Tendsto (fun r => -DW r / (2 * Real.sqrt (-W r))) l atBot := by
    have h := hnum.neg_mul_atTop (by norm_num : (-(1 / 648) : ℝ) < 0) hinv
    simpa only [div_eq_mul_inv] using h
  apply hquot.congr'
  filter_upwards [h3, hbelow] with r hr3 hr6
  have hr0 : r ≠ 0 := by linarith
  have hr3' : r ≠ 3 := by linarith
  have hW : W r ≠ 0 := by
    intro h
    have := (W_eq_zero_iff_of_three_lt hr3).1 h
    linarith
  exact (deriv_growingEigenvalue r hr0 hr3' hW).symm

end

/-! ## The derivative ambiguity, certified

`V''` in the manuscript is the second partial in `r` at fixed `L^2`, substituted afterwards at the
circular value. The second derivative *along* the family `r |-> V(r, circular r)` is a different
number, and at the ISCO it is not zero. The two readings are distinguished below so that the wall
cannot be attributed to the wrong derivative.
-/

lemma hasDerivAt_V_fixed (Lam r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s => V s Lam)
      (2 / r ^ 2 - 2 * Lam / r ^ 3 + 6 * Lam / r ^ 4) r := by
  unfold V
  convert (((hasDerivAt_const r (1 : ℝ)).sub
      ((hasDerivAt_const r (2 : ℝ)).div (hasDerivAt_id r) hr)).mul
    ((hasDerivAt_const r (1 : ℝ)).add
      ((hasDerivAt_const r Lam).div ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr)))) using 1
  · funext s
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply,
      Pi.pow_apply, Pi.one_apply, Pi.zero_apply, Pi.ofNat_apply, id_eq]
  · norm_num
    field_simp
    ring


lemma hasDerivAt_radialFirst (Lam r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s => 2 / s ^ 2 - 2 * Lam / s ^ 3 + 6 * Lam / s ^ 4)
      (6 * Lam / r ^ 4 - 24 * Lam / r ^ 5 - 4 / r ^ 3) r := by
  convert ((((hasDerivAt_const r (2 : ℝ)).div ((hasDerivAt_id r).pow 2)
      (pow_ne_zero 2 hr)).sub
    ((hasDerivAt_const r (2 * Lam)).div ((hasDerivAt_id r).pow 3)
      (pow_ne_zero 3 hr))).add
    ((hasDerivAt_const r (6 * Lam)).div ((hasDerivAt_id r).pow 4)
      (pow_ne_zero 4 hr))) using 1
  · funext s
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply,
      Pi.pow_apply, Pi.one_apply, Pi.zero_apply, Pi.ofNat_apply, id_eq]
  · norm_num
    field_simp
    ring

/-- The second radial derivative at fixed `Lam`, exactly as in the manuscript. -/
theorem second_partial_V (Lam r : ℝ) (hr : r ≠ 0) :
    deriv (deriv (fun s => V s Lam)) r =
      6 * Lam / r ^ 4 - 24 * Lam / r ^ 5 - 4 / r ^ 3 := by
  have heq : (deriv (fun s => V s Lam)) =ᶠ[𝓝 r]
      (fun s => 2 / s ^ 2 - 2 * Lam / s ^ 3 + 6 * Lam / s ^ 4) := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact (hasDerivAt_V_fixed Lam s hs).deriv
  calc
    deriv (deriv (fun s => V s Lam)) r =
        deriv (fun s => 2 / s ^ 2 - 2 * Lam / s ^ 3 + 6 * Lam / s ^ 4) r :=
      heq.deriv_eq
    _ = _ := (hasDerivAt_radialFirst Lam r hr).deriv

/-- After differentiation, substitution on the circular family gives `2 * W`. -/
theorem second_partial_V_circular (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3) :
    deriv (deriv (fun s => V s (circular r))) r = 2 * W r := by
  rw [second_partial_V _ r hr]
  simp only [circular, W]
  field_simp [hr, sub_ne_zero.mpr hr3]
  ring

/-- Equivalent half-coefficient form: the potential term in the generator is `W`. -/
theorem half_second_partial_V_circular (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3) :
    (1 / 2) * deriv (deriv (fun s => V s (circular r))) r = W r := by
  rw [second_partial_V_circular r hr hr3]
  ring

/-- In particular, the fixed-angular-momentum second partial vanishes at the ISCO. -/
theorem second_partial_V_at_ISCO :
    deriv (deriv (fun s => V s (circular 6))) 6 = 0 := by
  rw [second_partial_V_circular 6 (by norm_num) (by norm_num)]
  norm_num [W]

lemma family_reduced (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3) :
    V r (circular r) = (r - 2) ^ 2 / (r * (r - 3)) := by
  simp only [V, circular]
  field_simp [hr, sub_ne_zero.mpr hr3]
  ring

lemma hasDerivAt_reducedFamily (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3) :
    HasDerivAt (fun s => (s - 2) ^ 2 / (s * (s - 3)))
      ((r - 6) * (r - 2) / (r ^ 2 * (r - 3) ^ 2)) r := by
  convert (((hasDerivAt_id r).sub (hasDerivAt_const r (2 : ℝ))).pow 2).div
    ((hasDerivAt_id r).mul ((hasDerivAt_id r).sub (hasDerivAt_const r (3 : ℝ))))
    (mul_ne_zero hr (sub_ne_zero.mpr hr3)) using 1
  · funext s
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply,
      Pi.pow_apply, Pi.one_apply, Pi.zero_apply, Pi.ofNat_apply, id_eq]
  · norm_num
    field_simp [hr, sub_ne_zero.mpr hr3]
    ring

lemma hasDerivAt_family (r : ℝ) (hr : r ≠ 0) (hr3 : r ≠ 3) :
    HasDerivAt (fun s => V s (circular s))
      ((r - 6) * (r - 2) / (r ^ 2 * (r - 3) ^ 2)) r := by
  apply (hasDerivAt_reducedFamily r hr hr3).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hr, eventually_ne_nhds hr3] with s hs hs3
  exact family_reduced s hs hs3

lemma hasDerivAt_familyFirst_at_ISCO :
    HasDerivAt (fun s : ℝ => (s - 6) * (s - 2) / (s ^ 2 * (s - 3) ^ 2))
      (1 / 81 : ℝ) 6 := by
  convert (((hasDerivAt_id (6 : ℝ)).sub (hasDerivAt_const 6 (6 : ℝ))).mul
    ((hasDerivAt_id 6).sub (hasDerivAt_const 6 (2 : ℝ)))).div
    (((hasDerivAt_id (6 : ℝ)).pow 2).mul
      (((hasDerivAt_id 6).sub (hasDerivAt_const 6 (3 : ℝ))).pow 2))
    (by norm_num) using 1
  · funext s
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply,
      Pi.pow_apply, Pi.one_apply, Pi.zero_apply, Pi.ofNat_apply, id_eq]
  · norm_num

/-- The second derivative *after* substituting the varying circular angular momentum.
This is not the fixed-`Lam` second partial in `second_partial_V_at_ISCO`. -/
theorem second_total_family_at_ISCO :
    deriv (deriv (fun s => V s (circular s))) 6 = 1 / 81 := by
  have heq : (deriv (fun s => V s (circular s))) =ᶠ[𝓝 (6 : ℝ)]
      (fun s => (s - 6) * (s - 2) / (s ^ 2 * (s - 3) ^ 2)) := by
    filter_upwards [eventually_ne_nhds (show (6 : ℝ) ≠ 0 by norm_num),
      eventually_ne_nhds (show (6 : ℝ) ≠ 3 by norm_num)] with s hs hs3
    exact (hasDerivAt_family s hs hs3).deriv
  calc
    deriv (deriv (fun s => V s (circular s))) 6 =
        deriv (fun s => (s - 6) * (s - 2) / (s ^ 2 * (s - 3) ^ 2)) 6 := heq.deriv_eq
    _ = 1 / 81 := hasDerivAt_familyFirst_at_ISCO.deriv

/-- A formal certificate that the two derivative meanings differ at `r = 6`. -/
theorem partial_ne_total_at_ISCO :
    deriv (deriv (fun s => V s (circular 6))) 6 ≠
      deriv (deriv (fun s => V s (circular s))) 6 := by
  rw [second_partial_V_at_ISCO, second_total_family_at_ISCO]
  norm_num


end SpectralWall
