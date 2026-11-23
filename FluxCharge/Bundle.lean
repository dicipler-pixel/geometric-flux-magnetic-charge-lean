import FluxCharge.Geometry

/-!
# `FluxCharge.Bundle` — the lower eigenline bundle in two charts

Paper v5, §4, writes down the local eigenvectors

`u_N = (−e^{−iφ} sin(θ/2), cos(θ/2))`,  `u_S = (−sin(θ/2), e^{iφ} cos(θ/2))`,

notes that `H(n) u = −u` and `u_S = e^{iφ} u_N` on the overlap, and states the resulting
coefficients `a_N = (1 − cos θ)/2`, `a_S = −(1 + cos θ)/2`. Version 5 checks only the
*scalar* identities `a_N' = a_S' = ω` and `a_N − a_S = 1` for those coefficients supplied by
hand (`north_derivative`, `south_derivative`, `gauge_coefficient_difference`), and says so:
"the companion code does not construct that bundle, its transition-function winding, or its
Chern class."

This module supplies the objects the writing uses:

* `uN`, `uS` are the two sections; each has unit norm (`uN_norm`, `uS_norm`) and is a lower
  eigenvector of the Pauli matrix along `n(θ,φ)` (`pauli_mulVec_uN`, `pauli_mulVec_uS`), hence
  lies in the range of the lower projector (`proj_mulVec_uN`, `proj_mulVec_uS`).
* `uS_eq_smul_uN` is the transition function `e^{iφ}` on the overlap, and
  `transition_winding` computes its winding number as 1.
* `berryConnection_uN` and `berryConnection_uS` compute the Berry connection `i u† du` from
  Lean's `deriv` of the actual section components and get `northCoefficient` and
  `southCoefficient`. In v5 those coefficients were supplied; here they are derived from the
  sections.
* `connection_gauge_difference` and `curvature_from_connection` turn `a_N − a_S = 1` and
  `a_N' = ω` into statements about one connection read in two charts, and the curvature agrees
  with `Monopole.berry_curvature`.
* `bundle_normalized_flux` and `chern_number_one` record the flux normalization `1`, which is
  also the winding of the transition function.

Not proved here (the remaining boundaries of the paper): an abstract first Chern class or
Chern–Weil theory, general coordinate and gauge invariance, integer-valuedness of winding
numbers for arbitrary circle maps, spatial pullbacks with their degree formula, and any
electromagnetic identification.
-/

namespace MonopoleStance

noncomputable section

open Matrix Complex
open scoped Real ComplexConjugate

set_option maxHeartbeats 1000000

/-! ## The two local sections of the lower eigenline -/

/-- Northern-chart unit section of the lower eigenline; regular away from the south pole. -/
def uN (θ φ : ℝ) : Fin 2 → ℂ :=
  ![-(Real.sin (θ / 2) : ℂ) * Complex.exp (-(I * (φ : ℂ))), (Real.cos (θ / 2) : ℂ)]

/-- Southern-chart unit section of the lower eigenline; regular away from the north pole. -/
def uS (θ φ : ℝ) : Fin 2 → ℂ :=
  ![(-(Real.sin (θ / 2)) : ℂ), (Real.cos (θ / 2) : ℂ) * Complex.exp (I * (φ : ℂ))]

/-- Squared norm of a spinor, `|u₀|² + |u₁|²`. -/
def spinorNormSq (u : Fin 2 → ℂ) : ℝ := Complex.normSq (u 0) + Complex.normSq (u 1)

/-- The transition (clutching) phase `e^{iφ}` relating the two charts. -/
def transitionPhase (φ : ℝ) : ℂ := Complex.exp (I * (φ : ℂ))

/-- The Berry connection `i u† ∂_φ u` of a one-parameter family of spinors, built from Lean's
`deriv` of the actual component functions. -/
def berryConnection (u : ℝ → Fin 2 → ℂ) (φ : ℝ) : ℝ :=
  (I * (conj (u φ 0) * deriv (fun t => u t 0) φ +
        conj (u φ 1) * deriv (fun t => u t 1) φ)).re

/-! ## Rows of the matrix action -/

theorem pauli_row0 (a : Vec3) (v : Fin 2 → ℂ) :
    (pauli a *ᵥ v) 0 = (a.2.2 : ℂ) * v 0 + ((a.1 : ℂ) - I * (a.2.1 : ℂ)) * v 1 := by
  simp [pauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem pauli_row1 (a : Vec3) (v : Fin 2 → ℂ) :
    (pauli a *ᵥ v) 1 = ((a.1 : ℂ) + I * (a.2.1 : ℂ)) * v 0 - (a.2.2 : ℂ) * v 1 := by
  simp [pauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem proj_row0 (n : Vec3) (v : Fin 2 → ℂ) :
    (proj n *ᵥ v) 0 =
      (((1 - n.2.2) / 2 : ℝ) : ℂ) * v 0 + (-((n.1 : ℂ) - I * (n.2.1 : ℂ)) / 2) * v 1 := by
  simp [proj, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem proj_row1 (n : Vec3) (v : Fin 2 → ℂ) :
    (proj n *ᵥ v) 1 =
      (-((n.1 : ℂ) + I * (n.2.1 : ℂ)) / 2) * v 0 + (((1 + n.2.2) / 2 : ℝ) : ℂ) * v 1 := by
  simp [proj, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The projector is `(1/2)(1 − n·σ)`. -/
theorem proj_eq_smul (n : Vec3) : proj n = (2 : ℂ)⁻¹ • (1 - pauli n) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj, pauli, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] <;>
    push_cast <;> ring

/-! ## Half-angle trigonometry and the two exponentials -/

theorem sin_two_mul_half (θ : ℝ) : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
  have h := Real.sin_two_mul (θ / 2)
  rwa [show 2 * (θ / 2) = θ by ring] at h

theorem cos_two_mul_half (θ : ℝ) :
    Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul' (θ / 2)
  rwa [show 2 * (θ / 2) = θ by ring] at h

theorem exp_neg_I_mul (φ : ℝ) :
    Complex.exp (-(I * (φ : ℂ))) = (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * I := by
  have h : -(I * (φ : ℂ)) = ((-φ : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

theorem exp_I_mul (φ : ℝ) :
    Complex.exp (I * (φ : ℂ)) = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * I := by
  have h : I * (φ : ℂ) = ((φ : ℝ) : ℂ) * I := by ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-! ## The unit direction and the sections in component form -/

theorem dot_nvec (θ φ : ℝ) : dot (nvec θ φ) (nvec θ φ) = 1 := by
  simp only [dot, nvec]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

theorem nvec_half (θ φ : ℝ) :
    nvec θ φ = (2 * Real.sin (θ / 2) * Real.cos (θ / 2) * Real.cos φ,
                2 * Real.sin (θ / 2) * Real.cos (θ / 2) * Real.sin φ,
                Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) := by
  simp only [nvec]
  rw [sin_two_mul_half θ, cos_two_mul_half θ]

theorem uN_eq (θ φ : ℝ) :
    uN θ φ = ![(-(Real.sin (θ / 2) : ℂ) * (Real.cos φ : ℂ) +
                  (Real.sin (θ / 2) : ℂ) * (Real.sin φ : ℂ) * I), (Real.cos (θ / 2) : ℂ)] := by
  ext i
  fin_cases i <;> simp [uN, exp_neg_I_mul] <;> ring

theorem uS_eq (θ φ : ℝ) :
    uS θ φ = ![(-(Real.sin (θ / 2)) : ℂ),
                (Real.cos (θ / 2) : ℂ) * (Real.cos φ : ℂ) +
                  (Real.cos (θ / 2) : ℂ) * (Real.sin φ : ℂ) * I] := by
  ext i
  fin_cases i <;> simp [uS, exp_I_mul] <;> ring

/-! ## The sections are lower eigenvectors -/

/-- Row `0` of `(n(θ,φ)·σ) u_N = −u_N`, in half-angle form. -/
theorem eigen_row0 (s c cf sf : ℝ) (hs : s ^ 2 + c ^ 2 = 1) (hp : cf ^ 2 + sf ^ 2 = 1) :
    (pauli (2 * s * c * cf, 2 * s * c * sf, c ^ 2 - s ^ 2) *ᵥ
        ![(-((s : ℂ) * (cf : ℂ)) + (s : ℂ) * (sf : ℂ) * I), (c : ℂ)]) 0
      = -(-((s : ℂ) * (cf : ℂ)) + (s : ℂ) * (sf : ℂ) * I) := by
  rw [pauli_row0]
  apply Complex.ext
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    push_cast
    ring_nf
    linear_combination (s * cf) * hs
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    push_cast
    ring_nf
    linear_combination (-(s * sf)) * hs

/-- Row `1` of `(n(θ,φ)·σ) u_N = −u_N`, in half-angle form. -/
theorem eigen_row1 (s c cf sf : ℝ) (hs : s ^ 2 + c ^ 2 = 1) (hp : cf ^ 2 + sf ^ 2 = 1) :
    (pauli (2 * s * c * cf, 2 * s * c * sf, c ^ 2 - s ^ 2) *ᵥ
        ![(-((s : ℂ) * (cf : ℂ)) + (s : ℂ) * (sf : ℂ) * I), (c : ℂ)]) 1 = -(c : ℂ) := by
  rw [pauli_row1]
  apply Complex.ext
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    push_cast
    ring_nf
    linear_combination (-2 * s ^ 2 * c) * hp + (-c) * hs
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    push_cast
    ring

/-- Row `0` of `(n(θ,φ)·σ) u_S = −u_S`, in half-angle form. -/
theorem eigen_row0_S (s c cf sf : ℝ) (hs : s ^ 2 + c ^ 2 = 1) (hp : cf ^ 2 + sf ^ 2 = 1) :
    (pauli (2 * s * c * cf, 2 * s * c * sf, c ^ 2 - s ^ 2) *ᵥ
        ![(-(s : ℂ)), ((c : ℂ) * (cf : ℂ) + (c : ℂ) * (sf : ℂ) * I)]) 0 = (s : ℂ) := by
  rw [pauli_row0]
  apply Complex.ext
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    push_cast
    ring_nf
    linear_combination (s) * hs + (2 * s * c ^ 2) * hp
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    push_cast
    ring

/-- Row `1` of `(n(θ,φ)·σ) u_S = −u_S`, in half-angle form. -/
theorem eigen_row1_S (s c cf sf : ℝ) (hs : s ^ 2 + c ^ 2 = 1) (hp : cf ^ 2 + sf ^ 2 = 1) :
    (pauli (2 * s * c * cf, 2 * s * c * sf, c ^ 2 - s ^ 2) *ᵥ
        ![(-(s : ℂ)), ((c : ℂ) * (cf : ℂ) + (c : ℂ) * (sf : ℂ) * I)]) 1
      = -((c : ℂ) * (cf : ℂ) + (c : ℂ) * (sf : ℂ) * I) := by
  rw [pauli_row1]
  apply Complex.ext
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    push_cast
    ring_nf
    linear_combination (-(c * cf)) * hs
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    push_cast
    ring_nf
    linear_combination (-(c * sf)) * hs

/-! ## The sections are lower eigenvectors and have unit norm -/

theorem half_trig_sin (θ : ℝ) : Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq (θ / 2)

theorem half_trig_cos (θ : ℝ) : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := by
  linarith [Real.sin_sq_add_cos_sq (θ / 2)]

/-- The northern section is a lower eigenvector of `n(θ,φ)·σ`. -/
theorem pauli_mulVec_uN (θ φ : ℝ) : pauli (nvec θ φ) *ᵥ uN θ φ = -uN θ φ := by
  rw [nvec_half θ φ, uN_eq θ φ]
  funext i
  fin_cases i
  · simpa using eigen_row0 (Real.sin (θ / 2)) (Real.cos (θ / 2)) (Real.cos φ) (Real.sin φ)
      (half_trig_sin θ) (by linarith [Real.sin_sq_add_cos_sq φ])
  · simpa using eigen_row1 (Real.sin (θ / 2)) (Real.cos (θ / 2)) (Real.cos φ) (Real.sin φ)
      (half_trig_sin θ) (by linarith [Real.sin_sq_add_cos_sq φ])

/-- The southern section is a lower eigenvector of `n(θ,φ)·σ`. -/
theorem pauli_mulVec_uS (θ φ : ℝ) : pauli (nvec θ φ) *ᵥ uS θ φ = -uS θ φ := by
  rw [nvec_half θ φ, uS_eq θ φ]
  funext i
  fin_cases i
  · simpa using eigen_row0_S (Real.sin (θ / 2)) (Real.cos (θ / 2)) (Real.cos φ) (Real.sin φ)
      (half_trig_sin θ) (by linarith [Real.sin_sq_add_cos_sq φ])
  · simpa using eigen_row1_S (Real.sin (θ / 2)) (Real.cos (θ / 2)) (Real.cos φ) (Real.sin φ)
      (half_trig_sin θ) (by linarith [Real.sin_sq_add_cos_sq φ])

/-- Both sections lie in the range of the lower projector `P = (1/2)(1 − n·σ)`. -/
theorem proj_mulVec_uN (θ φ : ℝ) : proj (nvec θ φ) *ᵥ uN θ φ = uN θ φ := by
  rw [proj_eq_smul, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    pauli_mulVec_uN]
  rw [sub_neg_eq_add, ← two_smul ℂ, smul_smul]
  norm_num

theorem proj_mulVec_uS (θ φ : ℝ) : proj (nvec θ φ) *ᵥ uS θ φ = uS θ φ := by
  rw [proj_eq_smul, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    pauli_mulVec_uS]
  rw [sub_neg_eq_add, ← two_smul ℂ, smul_smul]
  norm_num

theorem uN_zero (θ φ : ℝ) :
    uN θ φ 0 = -(Real.sin (θ / 2) : ℂ) * Complex.exp (-(I * (φ : ℂ))) := rfl

theorem uN_one (θ φ : ℝ) : uN θ φ 1 = (Real.cos (θ / 2) : ℂ) := rfl

theorem uS_zero (θ φ : ℝ) : uS θ φ 0 = (-(Real.sin (θ / 2)) : ℂ) := rfl

theorem uS_one (θ φ : ℝ) : uS θ φ 1 = (Real.cos (θ / 2) : ℂ) * Complex.exp (I * (φ : ℂ)) := rfl

theorem normSq_exp_neg (φ : ℝ) : Complex.normSq (Complex.exp (-(I * (φ : ℂ)))) = 1 := by
  rw [exp_neg_I_mul]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem normSq_exp_pos (φ : ℝ) : Complex.normSq (Complex.exp (I * (φ : ℂ))) = 1 := by
  rw [exp_I_mul]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem uN_normSq (θ φ : ℝ) : spinorNormSq (uN θ φ) = 1 := by
  rw [spinorNormSq, uN_zero, uN_one, Complex.normSq_mul, Complex.normSq_neg,
    Complex.normSq_ofReal, normSq_exp_neg, Complex.normSq_ofReal]
  have := half_trig_sin θ
  nlinarith

theorem uS_normSq (θ φ : ℝ) : spinorNormSq (uS θ φ) = 1 := by
  rw [spinorNormSq, uS_zero, uS_one, Complex.normSq_mul, Complex.normSq_neg,
    Complex.normSq_ofReal, normSq_exp_pos, Complex.normSq_ofReal]
  have := half_trig_sin θ
  nlinarith


/-! ## The transition function: differentiability, winding, periodicity -/

lemma sin_half_sq (θ : ℝ) : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
  calc
    Real.sin (θ / 2) ^ 2 = 1 / 2 - Real.cos (2 * (θ / 2)) / 2 :=
      Real.sin_sq_eq_half_sub _
    _ = (1 - Real.cos θ) / 2 := by ring_nf

lemma cos_half_sq (θ : ℝ) : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
  calc
    Real.cos (θ / 2) ^ 2 = 1 / 2 + Real.cos (2 * (θ / 2)) / 2 := Real.cos_sq _
    _ = (1 + Real.cos θ) / 2 := by ring_nf

lemma hasDerivAt_transitionPhase (φ : ℝ) : HasDerivAt transitionPhase (I * transitionPhase φ) φ := by
  have h : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I φ := by
    simpa using (hasDerivAt_id φ).ofReal_comp.const_mul I
  simpa only [transitionPhase, mul_comm (Complex.exp _)] using! h.cexp

lemma deriv_transitionPhase (φ : ℝ) : deriv transitionPhase φ = I * transitionPhase φ :=
  (hasDerivAt_transitionPhase φ).deriv

lemma conj_transitionPhase (φ : ℝ) : conj (transitionPhase φ) = Complex.exp (-(I * (φ : ℂ))) := by
  rw [transitionPhase, ← Complex.exp_conj]
  congr 1
  simp

lemma conj_transitionPhase_mul_transitionPhase (φ : ℝ) : conj (transitionPhase φ) * transitionPhase φ = 1 := by
  rw [conj_transitionPhase, transitionPhase, ← Complex.exp_add]
  simp

lemma transitionPhase_norm (φ : ℝ) : ‖transitionPhase φ‖ = 1 := by
  simp [transitionPhase]

lemma transitionPhase_periodic : Function.Periodic transitionPhase (2 * Real.pi) := by
  intro φ
  simpa only [transitionPhase, mul_comm I, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using Complex.exp_mul_I_periodic φ

lemma hasDerivAt_exp_neg_I_mul (φ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(I * (t : ℂ))))
      (-I * Complex.exp (-(I * (φ : ℂ)))) φ := by
  have h : HasDerivAt (fun t : ℝ => -(I * (t : ℂ))) (-I) φ := by
    convert ((hasDerivAt_id φ).ofReal_comp.const_mul I).neg using 1 <;> simp [id]
    funext t
    rfl
  simpa only [mul_comm (Complex.exp _)] using! h.cexp

lemma hasDerivAt_exp_I_mul (φ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (I * (t : ℂ)))
      (I * Complex.exp (I * (φ : ℂ))) φ := by
  simpa only [transitionPhase] using! hasDerivAt_transitionPhase φ

lemma transitionPhase_winding_density (φ : ℝ) :
    (-I * (conj (transitionPhase φ) * deriv transitionPhase φ)).re = 1 := by
  rw [deriv_transitionPhase]
  have hc : conj (transitionPhase φ) * (I * transitionPhase φ) = I := by
    rw [← mul_assoc, mul_comm (conj (transitionPhase φ)) I, mul_assoc, conj_transitionPhase_mul_transitionPhase,
      mul_one]
  rw [hc]
  simp

lemma transitionPhase_winding_density_plus_I (φ : ℝ) :
    (I * (conj (transitionPhase φ) * deriv transitionPhase φ)).re = -1 := by
  rw [deriv_transitionPhase]
  have hc : conj (transitionPhase φ) * (I * transitionPhase φ) = I := by
    rw [← mul_assoc, mul_comm (conj (transitionPhase φ)) I, mul_assoc, conj_transitionPhase_mul_transitionPhase,
      mul_one]
  rw [hc]
  simp

lemma transitionPhase_winding_integral :
    (1 / (2 * Real.pi)) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
      (-I * (conj (transitionPhase φ) * deriv transitionPhase φ)).re = 1 := by
  simp_rw [transitionPhase_winding_density]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one, sub_zero]
  field_simp

lemma transitionPhase_winding_integral_plus_I :
    (1 / (2 * Real.pi)) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
      (I * (conj (transitionPhase φ) * deriv transitionPhase φ)).re = -1 := by
  simp_rw [transitionPhase_winding_density_plus_I]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_neg, mul_one, sub_zero]
  field_simp

lemma flux_theta : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ / 2 = 1 := by
  rw [intervalIntegral.integral_div]
  norm_num

lemma flux_two_pi : ∫ _φ in (0 : ℝ)..(2 * Real.pi),
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ / 2) = 2 * Real.pi := by
  rw [flux_theta, intervalIntegral.integral_const]
  simp

lemma chern_one :
    (1 / (2 * Real.pi)) * ∫ _φ in (0 : ℝ)..(2 * Real.pi),
      (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ / 2) = 1 := by
  rw [flux_two_pi]
  field_simp

lemma hasDerivAt_uN_zero (θ φ : ℝ) :
    HasDerivAt (fun t => uN θ t 0)
      ((-(Real.sin (θ / 2)) : ℂ) * (-I * Complex.exp (-(I * (φ : ℂ))))) φ := by
  simpa only [uN, Matrix.cons_val_zero] using!
    (hasDerivAt_exp_neg_I_mul φ).const_mul (-(Real.sin (θ / 2)) : ℂ)

lemma hasDerivAt_uN_one (θ φ : ℝ) :
    HasDerivAt (fun t => uN θ t 1) 0 φ := by
  simpa only [uN, Matrix.cons_val_one, Matrix.cons_val_zero] using
    (hasDerivAt_const φ (Real.cos (θ / 2) : ℂ))

lemma hasDerivAt_uS_zero (θ φ : ℝ) :
    HasDerivAt (fun t => uS θ t 0) 0 φ := by
  simpa only [uS, Matrix.cons_val_zero] using
    (hasDerivAt_const φ (-(Real.sin (θ / 2)) : ℂ))

lemma hasDerivAt_uS_one (θ φ : ℝ) :
    HasDerivAt (fun t => uS θ t 1)
      ((Real.cos (θ / 2) : ℂ) * (I * Complex.exp (I * (φ : ℂ)))) φ := by
  simpa only [uS, Matrix.cons_val_one, Matrix.cons_val_zero] using!
    (hasDerivAt_exp_I_mul φ).const_mul (Real.cos (θ / 2) : ℂ)

lemma deriv_uN_zero (θ φ : ℝ) :
    deriv (fun t => uN θ t 0) φ =
      (-(Real.sin (θ / 2)) : ℂ) * (-I * Complex.exp (-(I * (φ : ℂ)))) :=
  (hasDerivAt_uN_zero θ φ).deriv

lemma deriv_uN_one (θ φ : ℝ) : deriv (fun t => uN θ t 1) φ = 0 :=
  (hasDerivAt_uN_one θ φ).deriv

lemma deriv_uS_zero (θ φ : ℝ) : deriv (fun t => uS θ t 0) φ = 0 :=
  (hasDerivAt_uS_zero θ φ).deriv

lemma deriv_uS_one (θ φ : ℝ) :
    deriv (fun t => uS θ t 1) φ =
      (Real.cos (θ / 2) : ℂ) * (I * Complex.exp (I * (φ : ℂ))) :=
  (hasDerivAt_uS_one θ φ).deriv


lemma conj_exp_I (φ : ℝ) :
    conj (Complex.exp (I * (φ : ℂ))) = Complex.exp (-(I * (φ : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

lemma conj_exp_neg_I (φ : ℝ) :
    conj (Complex.exp (-(I * (φ : ℂ)))) = Complex.exp (I * (φ : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

lemma conj_exp_neg_I_mul_self (φ : ℝ) :
    conj (Complex.exp (-(I * (φ : ℂ)))) * Complex.exp (-(I * (φ : ℂ))) = 1 := by
  rw [conj_exp_neg_I, ← Complex.exp_add]
  simp

lemma conj_exp_I_mul_self (φ : ℝ) :
    conj (Complex.exp (I * (φ : ℂ))) * Complex.exp (I * (φ : ℂ)) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

lemma berry_exp_neg (s : ℝ) (z : ℂ) (hz : conj z * z = 1) :
    (I * (conj ((-(s : ℝ) : ℂ) * z) * ((-(s : ℝ) : ℂ) * (-I * z)))).re = s ^ 2 := by
  simp only [map_mul, map_neg, Complex.conj_ofReal]
  calc
    (I * ((-(s : ℂ) * conj z) * (-(s : ℂ) * (-I * z)))).re =
        (I * (((s : ℂ) ^ 2 * (-I)) * (conj z * z))).re := by
          congr 2
          ring
    _ = s ^ 2 := by rw [hz]; simp; norm_cast

lemma berry_exp_pos (c : ℝ) (z : ℂ) (hz : conj z * z = 1) :
    (I * (conj ((c : ℂ) * z) * ((c : ℂ) * (I * z)))).re = -c ^ 2 := by
  simp only [map_mul, Complex.conj_ofReal]
  calc
    (I * (((c : ℂ) * conj z) * ((c : ℂ) * (I * z)))).re =
        (I * (((c : ℂ) ^ 2 * I) * (conj z * z))).re := by
          congr 2
          ring
    _ = -c ^ 2 := by rw [hz]; simp; norm_cast

/-- The northern Berry connection in the `φ` direction. -/
def AN (θ φ : ℝ) : ℝ :=
  (I * (conj (uN θ φ 0) * deriv (fun t => uN θ t 0) φ +
    conj (uN θ φ 1) * deriv (fun t => uN θ t 1) φ)).re

/-- The southern Berry connection in the `φ` direction. -/
def AS (θ φ : ℝ) : ℝ :=
  (I * (conj (uS θ φ 0) * deriv (fun t => uS θ t 0) φ +
    conj (uS θ φ 1) * deriv (fun t => uS θ t 1) φ)).re

lemma AN_eq_sin_sq (θ φ : ℝ) : AN θ φ = Real.sin (θ / 2) ^ 2 := by
  unfold AN
  rw [deriv_uN_zero, deriv_uN_one]
  simp only [uN, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
  exact berry_exp_neg _ _ (conj_exp_neg_I_mul_self φ)

lemma AN_eq_half (θ φ : ℝ) : AN θ φ = (1 - Real.cos θ) / 2 := by
  rw [AN_eq_sin_sq, sin_half_sq]

lemma AN_independent (θ φ ψ : ℝ) : AN θ φ = AN θ ψ := by
  rw [AN_eq_sin_sq, AN_eq_sin_sq]

lemma AS_eq_neg_cos_sq (θ φ : ℝ) : AS θ φ = -Real.cos (θ / 2) ^ 2 := by
  unfold AS
  rw [deriv_uS_zero, deriv_uS_one]
  simp only [uS, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add]
  exact berry_exp_pos _ _ (conj_exp_I_mul_self φ)

lemma AS_eq_neg_half (θ φ : ℝ) : AS θ φ = -(1 + Real.cos θ) / 2 := by
  rw [AS_eq_neg_cos_sq, cos_half_sq]
  ring

lemma AS_independent (θ φ ψ : ℝ) : AS θ φ = AS θ ψ := by
  rw [AS_eq_neg_cos_sq, AS_eq_neg_cos_sq]

lemma gauge_difference (θ φ : ℝ) : AN θ φ - AS θ φ = 1 := by
  rw [AN_eq_sin_sq, AS_eq_neg_cos_sq]
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

lemma gauge_integral (θ : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), (AN θ φ - AS θ φ) = 2 * Real.pi := by
  simp_rw [gauge_difference]
  rw [intervalIntegral.integral_const]
  simp

lemma deriv_AN (θ φ : ℝ) : deriv (fun t => AN t φ) θ = Real.sin θ / 2 := by
  have hfun : (fun t => AN t φ) = (fun t => (1 - Real.cos t) / 2) := by
    funext t
    exact AN_eq_half t φ
  rw [hfun]
  simpa using (((hasDerivAt_const θ (1 : ℝ)).sub (Real.hasDerivAt_cos θ)).div_const 2)

/-! ## The transition function relating the two charts -/

theorem exp_mul_exp_neg (φ : ℝ) :
    Complex.exp (I * (φ : ℂ)) * Complex.exp (-(I * (φ : ℂ))) = 1 := by
  rw [← Complex.exp_add]
  ring_nf
  simp

theorem uS_eq_smul_uN_zero (θ φ : ℝ) :
    uS θ φ 0 = (transitionPhase φ • uN θ φ) 0 := by
  simp only [uS, uN, transitionPhase, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
  rw [show Complex.exp (I * (φ : ℂ)) *
        (-(Real.sin (θ / 2) : ℂ) * Complex.exp (-(I * (φ : ℂ)))) =
      -(Real.sin (θ / 2) : ℂ) *
        (Complex.exp (I * (φ : ℂ)) * Complex.exp (-(I * (φ : ℂ)))) from by ring]
  rw [exp_mul_exp_neg]
  ring

theorem uS_eq_smul_uN_one (θ φ : ℝ) :
    uS θ φ 1 = (transitionPhase φ • uN θ φ) 1 := by
  simp only [uS, uN, transitionPhase, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

/-- The southern section is the northern one multiplied by the transition phase `e^{iφ}`. -/
theorem uS_eq_smul_uN (θ φ : ℝ) : uS θ φ = transitionPhase φ • uN θ φ := by
  funext i
  fin_cases i
  · exact uS_eq_smul_uN_zero θ φ
  · exact uS_eq_smul_uN_one θ φ

/-! ## The two charts carry one connection -/

theorem berryConnection_uN_AN (θ φ : ℝ) : berryConnection (uN θ) φ = AN θ φ := rfl

theorem berryConnection_uS_AS (θ φ : ℝ) : berryConnection (uS θ) φ = AS θ φ := rfl

/-- The Berry connection of the northern section is the paper's coefficient `a_N`. -/
theorem berryConnection_uN (θ φ : ℝ) : berryConnection (uN θ) φ = northCoefficient θ := by
  rw [berryConnection_uN_AN, AN_eq_half]
  rfl

/-- The Berry connection of the southern section is the paper's coefficient `a_S`. -/
theorem berryConnection_uS (θ φ : ℝ) : berryConnection (uS θ) φ = southCoefficient θ := by
  rw [berryConnection_uS_AS, AS_eq_neg_half]
  rfl

/-- `A_N − A_S = 1` for the connections of two actual sections, not supplied coefficients. -/
theorem connection_gauge_difference (θ φ : ℝ) :
    berryConnection (uN θ) φ - berryConnection (uS θ) φ = 1 := by
  rw [berryConnection_uN, berryConnection_uS]
  exact gauge_coefficient_difference θ

/-- The curvature of the connection is the projector curvature `ω = sin θ / 2`. -/
theorem curvature_from_connection (θ : ℝ) :
    HasDerivAt (fun t : ℝ => berryConnection (uN t) 0) (omega θ) θ := by
  have hfun : (fun t : ℝ => berryConnection (uN t) 0) = northCoefficient := by
    funext t
    exact berryConnection_uN t 0
  rw [hfun]
  exact north_derivative θ

/-- The winding of the transition function, in the printed `-I` (equivalently `Im`) convention. -/
theorem transition_winding :
    (1 / (2 * Real.pi)) * (∫ φ in (0 : ℝ)..(2 * Real.pi),
      (-I * (conj (transitionPhase φ) * deriv transitionPhase φ)).re) = 1 :=
  transitionPhase_winding_integral

/-- Gauge difference one, winding one, normalized flux one. -/
theorem chern_number_one :
    (berryConnection (uN 0) 0 - berryConnection (uS 0) 0 = 1) ∧
    ((1 / (2 * Real.pi)) * (∫ φ in (0 : ℝ)..(2 * Real.pi),
      (-I * (conj (transitionPhase φ) * deriv transitionPhase φ)).re) = 1) ∧
    normalizedFlux omega = 1 :=
  ⟨connection_gauge_difference 0 0, transition_winding, omega_unit_normalizedFlux⟩

end

end MonopoleStance
