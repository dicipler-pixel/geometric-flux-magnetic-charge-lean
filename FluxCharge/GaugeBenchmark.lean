import Mathlib

/-!
# `FluxCharge.GaugeBenchmark` — the curvature identity is not vacuous, and its hypotheses bite

Companion to `FluxCharge.Gauge`, produced by the attacking side of a two-sided proof audit.

* `hopf_nonzero_benchmark` — for the explicit unit spinor `(cos a, e^{i b} sin a)` at `(π/4, 0)`
  both sides of the identity equal `-1`. Every other statement in these modules is conditional; this
  one shows the conditional statement says something.
* `curvature_identity_needs_differentiated_norm` — pointwise unit norm without tangency gives `2`
  against `0`.
* `curvature_identity_needs_unit_norm_despite_tangency` — both tangencies without unit norm give
  `-8` against `-128`.
-/

open scoped ComplexConjugate
open Complex Matrix

noncomputable section

namespace GaugeBenchmark

def badU (a b : ℝ) : Fin 2 → ℂ :=
  ![1 + (b : ℂ) + I * (a : ℂ), 0]

def proj (u : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u 0 * conj (u 0), u 0 * conj (u 1);
     u 1 * conj (u 0), u 1 * conj (u 1)]

def berryA (u : ℝ → ℝ → Fin 2 → ℂ) (a b : ℝ) : ℝ :=
  (I * (conj (u a b 0) * deriv (fun s => u s b 0) a +
    conj (u a b 1) * deriv (fun s => u s b 1) a)).re

def berryB (u : ℝ → ℝ → Fin 2 → ℂ) (a b : ℝ) : ℝ :=
  (I * (conj (u a b 0) * deriv (fun s => u a s 0) b +
    conj (u a b 1) * deriv (fun s => u a s 1) b)).re

example : conj (badU 0 0 0) * badU 0 0 0 + conj (badU 0 0 1) * badU 0 0 1 = 1 := by
  simp [badU]

example (a : ℝ) : deriv (fun s : ℝ => (s : ℂ)) a = 1 := by
  exact (Complex.ofRealCLM.hasDerivAt (x := a)).deriv

lemma badU_deriv_a_zero (a b : ℝ) : deriv (fun s => badU s b 0) a = I := by
  have ho : deriv (fun s : ℝ => (s : ℂ)) a = 1 :=
    (Complex.ofRealCLM.hasDerivAt (x := a)).deriv
  simp [badU, ho]

lemma badU_deriv_a_one (a b : ℝ) : deriv (fun s => badU s b 1) a = 0 := by
  simp [badU]

lemma badU_deriv_b_zero (a b : ℝ) : deriv (fun s => badU a s 0) b = 1 := by
  have ho : deriv (fun s : ℝ => (s : ℂ)) b = 1 :=
    (Complex.ofRealCLM.hasDerivAt (x := b)).deriv
  simp [badU, ho]

lemma badU_deriv_b_one (a b : ℝ) : deriv (fun s => badU a s 1) b = 0 := by
  simp [badU]

lemma bad_berryA (a b : ℝ) : berryA badU a b = -(1 + b) := by
  unfold berryA
  rw [badU_deriv_a_zero, badU_deriv_a_one]
  simp [badU, Complex.mul_re]

lemma bad_berryB (a b : ℝ) : berryB badU a b = a := by
  unfold berryB
  rw [badU_deriv_b_zero, badU_deriv_b_one]
  simp [badU, Complex.mul_re]

def curvature (u : ℝ → ℝ → Fin 2 → ℂ) (a b : ℝ) : ℝ :=
  deriv (fun s => berryB u s b) a - deriv (fun s => berryA u a s) b

def dPa (u : ℝ → ℝ → Fin 2 → ℂ) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => deriv (fun s => proj (u s b) i j) a

def dPb (u : ℝ → ℝ → Fin 2 → ℂ) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => deriv (fun s => proj (u a s) i j) b

lemma bad_curvature (a b : ℝ) : curvature badU a b = 2 := by
  simp [curvature, bad_berryA, bad_berryB]
  norm_num

lemma bad_dPa (a b : ℝ) : dPa badU a b =
    !![deriv (fun s => badU s b 0 * conj (badU s b 0)) a, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dPa, proj, badU]

lemma bad_dPb (a b : ℝ) : dPb badU a b =
    !![deriv (fun s => badU a s 0 * conj (badU a s 0)) b, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dPb, proj, badU]

lemma bad_projector_curvature (a b : ℝ) :
    (I * Matrix.trace (proj (badU a b) *
      (dPa badU a b * dPb badU a b - dPb badU a b * dPa badU a b))).re = 0 := by
  rw [bad_dPa, bad_dPb]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, proj]

/-- Unit norm at the evaluation point does not imply the projector-curvature formula. -/
theorem curvature_identity_needs_differentiated_norm :
    conj (badU 0 0 0) * badU 0 0 0 + conj (badU 0 0 1) * badU 0 0 1 = 1 ∧
    curvature badU 0 0 ≠
      (I * Matrix.trace (proj (badU 0 0) *
        (dPa badU 0 0 * dPb badU 0 0 - dPb badU 0 0 * dPa badU 0 0))).re := by
  constructor
  · simp [badU]
  · rw [bad_curvature, bad_projector_curvature]
    norm_num


/-- Rescaling preserves the origin's real tangency, but destroys unit norm. -/
def scaledU (a b : ℝ) : Fin 2 → ℂ :=
  ![2, 2 * (a : ℂ) + 2 * I * (b : ℂ)]

lemma scaledU_deriv_a_zero (a b : ℝ) : deriv (fun s => scaledU s b 0) a = 0 := by
  simp [scaledU]

lemma scaledU_deriv_a_one (a b : ℝ) : deriv (fun s => scaledU s b 1) a = 2 := by
  have ho : deriv (fun s : ℝ => (s : ℂ)) a = 1 :=
    (Complex.ofRealCLM.hasDerivAt (x := a)).deriv
  simp [scaledU, ho]

lemma scaledU_deriv_b_zero (a b : ℝ) : deriv (fun s => scaledU a s 0) b = 0 := by
  simp [scaledU]

lemma scaledU_deriv_b_one (a b : ℝ) : deriv (fun s => scaledU a s 1) b = 2 * I := by
  have ho : deriv (fun s : ℝ => (s : ℂ)) b = 1 :=
    (Complex.ofRealCLM.hasDerivAt (x := b)).deriv
  simp [scaledU, ho]

lemma scaled_berryA (a b : ℝ) : berryA scaledU a b = 4 * b := by
  unfold berryA
  rw [scaledU_deriv_a_zero, scaledU_deriv_a_one]
  simp [scaledU, Complex.mul_re]
  ring

lemma scaled_berryB (a b : ℝ) : berryB scaledU a b = -4 * a := by
  unfold berryB
  rw [scaledU_deriv_b_zero, scaledU_deriv_b_one]
  simp [scaledU, Complex.mul_re]
  ring

lemma scaled_curvature (a b : ℝ) : curvature scaledU a b = -8 := by
  simp [curvature, scaled_berryA, scaled_berryB]
  norm_num

lemma scaled_dPa_zero : dPa scaledU 0 0 = !![0, 4; 4, dPa scaledU 0 0 1 1] := by
  have ho : deriv (fun s : ℝ => (s : ℂ)) (0 : ℝ) = 1 :=
    (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).deriv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dPa, proj, scaledU, ho, Complex.conj_ofNat] <;> norm_num <;> ring

lemma scaled_dPb_zero : dPb scaledU 0 0 = !![0, -4 * I; 4 * I, dPb scaledU 0 0 1 1] := by
  have ho : deriv (fun s : ℝ => (s : ℂ)) (0 : ℝ) = 1 :=
    (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).deriv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dPb, proj, scaledU, ho, Complex.conj_ofNat] <;> norm_num <;> ring

lemma scaled_projector_curvature_zero :
    (I * Matrix.trace (proj (scaledU 0 0) *
      (dPa scaledU 0 0 * dPb scaledU 0 0 - dPb scaledU 0 0 * dPa scaledU 0 0))).re = -128 := by
  rw [scaled_dPa_zero, scaled_dPb_zero]
  simp [proj, scaledU, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re]
  ring

/-- Real tangency without unit norm does not imply the projector-curvature formula. -/
theorem curvature_identity_needs_unit_norm_despite_tangency :
    (conj (scaledU 0 0 0) * deriv (fun s => scaledU s 0 0) 0 +
      conj (scaledU 0 0 1) * deriv (fun s => scaledU s 0 1) 0).re = 0 ∧
    (conj (scaledU 0 0 0) * deriv (fun s => scaledU 0 s 0) 0 +
      conj (scaledU 0 0 1) * deriv (fun s => scaledU 0 s 1) 0).re = 0 ∧
    curvature scaledU 0 0 ≠
      (I * Matrix.trace (proj (scaledU 0 0) *
        (dPa scaledU 0 0 * dPb scaledU 0 0 - dPb scaledU 0 0 * dPa scaledU 0 0))).re := by
  rw [scaledU_deriv_a_zero, scaledU_deriv_a_one,
    scaledU_deriv_b_zero, scaledU_deriv_b_one, scaled_curvature,
    scaled_projector_curvature_zero]
  simp [scaledU]



/-- A smooth unit-norm spinor with nonzero Berry curvature. -/
noncomputable def hopfU (a b : ℝ) : Fin 2 → ℂ :=
  ![((Real.cos a : ℝ) : ℂ), Complex.exp (Complex.I * (b : ℂ)) * ((Real.sin a : ℝ) : ℂ)]

lemma phase_conj_mul (b : ℝ) :
    conj (Complex.exp (Complex.I * (b : ℂ))) * Complex.exp (Complex.I * (b : ℂ)) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

lemma hasDerivAt_phase (x : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (s : ℂ)))
      (Complex.I * Complex.exp (Complex.I * (x : ℂ))) x := by
  have hr : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x :=
    (Complex.ofRealCLM.hasDerivAt (x := x))
  have hI := hr.const_mul Complex.I
  convert hI.cexp using 1 <;> simp [mul_comm]

lemma hopf_hasDerivAt_a_zero (a b : ℝ) :
    HasDerivAt (fun s => hopfU s b 0) ((-Real.sin a : ℝ) : ℂ) a := by
  exact (Real.hasDerivAt_cos a).ofReal_comp

lemma hopf_hasDerivAt_a_one (a b : ℝ) :
    HasDerivAt (fun s => hopfU s b 1)
      (Complex.exp (Complex.I * (b : ℂ)) * ((Real.cos a : ℝ) : ℂ)) a := by
  exact (Real.hasDerivAt_sin a).ofReal_comp.const_mul _

lemma hopf_hasDerivAt_b_zero (a b : ℝ) :
    HasDerivAt (fun s => hopfU a s 0) 0 b := by
  exact hasDerivAt_const b _

lemma hopf_hasDerivAt_b_one (a b : ℝ) :
    HasDerivAt (fun s => hopfU a s 1)
      (Complex.I * Complex.exp (Complex.I * (b : ℂ)) * ((Real.sin a : ℝ) : ℂ)) b := by
  exact (hasDerivAt_phase b).mul_const _

lemma hopf_deriv_a_zero (a b : ℝ) : deriv (fun s => hopfU s b 0) a = ((-Real.sin a : ℝ) : ℂ) :=
  (hopf_hasDerivAt_a_zero a b).deriv

lemma hopf_deriv_a_one (a b : ℝ) : deriv (fun s => hopfU s b 1) a =
    Complex.exp (Complex.I * (b : ℂ)) * ((Real.cos a : ℝ) : ℂ) :=
  (hopf_hasDerivAt_a_one a b).deriv

lemma hopf_deriv_b_zero (a b : ℝ) : deriv (fun s => hopfU a s 0) b = 0 :=
  (hopf_hasDerivAt_b_zero a b).deriv

lemma hopf_deriv_b_one (a b : ℝ) : deriv (fun s => hopfU a s 1) b =
    Complex.I * Complex.exp (Complex.I * (b : ℂ)) * ((Real.sin a : ℝ) : ℂ) :=
  (hopf_hasDerivAt_b_one a b).deriv

lemma hopf_unit (a b : ℝ) :
    conj (hopfU a b 0) * hopfU a b 0 + conj (hopfU a b 1) * hopfU a b 1 = 1 := by
  have hz := phase_conj_mul b
  have ht := Real.sin_sq_add_cos_sq a
  simp only [hopfU, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    map_mul, Complex.conj_ofReal]
  calc
    _ = ((Real.cos a : ℝ) : ℂ) * ((Real.cos a : ℝ) : ℂ) +
        (conj (Complex.exp (Complex.I * (b : ℂ))) * Complex.exp (Complex.I * (b : ℂ))) *
          (((Real.sin a : ℝ) : ℂ) * ((Real.sin a : ℝ) : ℂ)) := by ring
    _ = (((Real.cos a) ^ 2 + (Real.sin a) ^ 2 : ℝ) : ℂ) := by
      rw [hz, one_mul]
      push_cast
      ring
    _ = 1 := by
      norm_cast
      nlinarith [ht]

lemma hopf_ip_a (a b : ℝ) :
    conj (hopfU a b 0) * deriv (fun s => hopfU s b 0) a +
      conj (hopfU a b 1) * deriv (fun s => hopfU s b 1) a = 0 := by
  rw [hopf_deriv_a_zero, hopf_deriv_a_one]
  simp only [hopfU, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, Complex.conj_ofReal]
  have hz := phase_conj_mul b
  calc
    _ = (conj (Complex.exp (Complex.I * (b : ℂ))) * Complex.exp (Complex.I * (b : ℂ)) - 1) *
        (((Real.sin a : ℝ) : ℂ) * ((Real.cos a : ℝ) : ℂ)) := by push_cast; ring
    _ = 0 := by rw [hz]; ring

lemma hopf_ip_b (a b : ℝ) :
    conj (hopfU a b 0) * deriv (fun s => hopfU a s 0) b +
      conj (hopfU a b 1) * deriv (fun s => hopfU a s 1) b =
        Complex.I * ((Real.sin a : ℝ) : ℂ) * ((Real.sin a : ℝ) : ℂ) := by
  rw [hopf_deriv_b_zero, hopf_deriv_b_one]
  simp only [hopfU, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, Complex.conj_ofReal]
  have hz := phase_conj_mul b
  calc
    _ = Complex.I * (conj (Complex.exp (Complex.I * (b : ℂ))) *
        Complex.exp (Complex.I * (b : ℂ))) *
          (((Real.sin a : ℝ) : ℂ) * ((Real.sin a : ℝ) : ℂ)) := by push_cast; ring
    _ = _ := by rw [hz]; ring

lemma hopf_tangent_a (a b : ℝ) :
    (conj (hopfU a b 0) * deriv (fun s => hopfU s b 0) a +
      conj (hopfU a b 1) * deriv (fun s => hopfU s b 1) a).re = 0 := by
  rw [hopf_ip_a]
  rfl

lemma hopf_tangent_b (a b : ℝ) :
    (conj (hopfU a b 0) * deriv (fun s => hopfU a s 0) b +
      conj (hopfU a b 1) * deriv (fun s => hopfU a s 1) b).re = 0 := by
  rw [hopf_ip_b]
  simp [Complex.mul_re, Complex.ofReal_re]

lemma hopf_berryA (a b : ℝ) : berryA hopfU a b = 0 := by
  unfold berryA
  rw [hopf_ip_a]
  simp

lemma hopf_berryB (a b : ℝ) : berryB hopfU a b = -(Real.sin a) ^ 2 := by
  unfold berryB
  rw [hopf_ip_b]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_one, mul_zero,
    sub_zero, zero_sub]
  ring

lemma hopf_curvature (a b : ℝ) : curvature hopfU a b = -2 * Real.sin a * Real.cos a := by
  have hsin : HasDerivAt (fun s : ℝ => -(Real.sin s) ^ 2)
      (-2 * Real.sin a * Real.cos a) a := by
    convert ((Real.hasDerivAt_sin a).pow 2).neg using 1 <;> ring
  simp only [curvature, hopf_berryA, hopf_berryB]
  rw [hsin.deriv, deriv_const]
  ring

lemma hopf_curvature_pi_div_four : curvature hopfU (Real.pi / 4) 0 = -1 := by
  rw [hopf_curvature, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

lemma hopf_dPa_b_zero (a : ℝ) : dPa hopfU a 0 =
    !![-2 * ((Real.sin a : ℝ) : ℂ) * ((Real.cos a : ℝ) : ℂ),
        ((Real.cos a : ℝ) : ℂ) * ((Real.cos a : ℝ) : ℂ) -
          ((Real.sin a : ℝ) : ℂ) * ((Real.sin a : ℝ) : ℂ);
        ((Real.cos a : ℝ) : ℂ) * ((Real.cos a : ℝ) : ℂ) -
          ((Real.sin a : ℝ) : ℂ) * ((Real.sin a : ℝ) : ℂ),
        2 * ((Real.sin a : ℝ) : ℂ) * ((Real.cos a : ℝ) : ℂ)] := by
  have hsin : conj (Complex.sin (a : ℂ)) = Complex.sin (a : ℂ) := by
    rw [← Complex.ofReal_sin, Complex.conj_ofReal]
  have hcos : conj (Complex.cos (a : ℂ)) = Complex.cos (a : ℂ) := by
    rw [← Complex.ofReal_cos, Complex.conj_ofReal]
  have h0 := hopf_hasDerivAt_a_zero a 0
  have h1 := hopf_hasDerivAt_a_one a 0
  have h00 : deriv (fun s => hopfU s 0 0 * conj (hopfU s 0 0)) a = _ :=
    (h0.mul h0.star).deriv
  have h01 : deriv (fun s => hopfU s 0 0 * conj (hopfU s 0 1)) a = _ :=
    (h0.mul h1.star).deriv
  have h10 : deriv (fun s => hopfU s 0 1 * conj (hopfU s 0 0)) a = _ :=
    (h1.mul h0.star).deriv
  have h11 : deriv (fun s => hopfU s 0 1 * conj (hopfU s 0 1)) a = _ :=
    (h1.mul h1.star).deriv
  ext i j
  fin_cases i <;> fin_cases j
  · change deriv (fun s => hopfU s 0 0 * conj (hopfU s 0 0)) a = _
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    rw [h00]
    simp [hopfU, hsin, hcos]
    ring
  · change deriv (fun s => hopfU s 0 0 * conj (hopfU s 0 1)) a = _
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    rw [h01]
    simp [hopfU, hsin, hcos]
    ring
  · change deriv (fun s => hopfU s 0 1 * conj (hopfU s 0 0)) a = _
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    rw [h10]
    simp [hopfU, hsin, hcos]
    ring
  · change deriv (fun s => hopfU s 0 1 * conj (hopfU s 0 1)) a = _
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    rw [h11]
    simp [hopfU, hsin, hcos]
    ring

lemma hopf_dPb_b_zero (a : ℝ) : dPb hopfU a 0 =
    !![0, -Complex.I * ((Real.cos a : ℝ) : ℂ) * ((Real.sin a : ℝ) : ℂ);
        Complex.I * ((Real.sin a : ℝ) : ℂ) * ((Real.cos a : ℝ) : ℂ), 0] := by
  have hsin : conj (Complex.sin (a : ℂ)) = Complex.sin (a : ℂ) := by
    rw [← Complex.ofReal_sin, Complex.conj_ofReal]
  have hcos : conj (Complex.cos (a : ℂ)) = Complex.cos (a : ℂ) := by
    rw [← Complex.ofReal_cos, Complex.conj_ofReal]
  have h0 := hopf_hasDerivAt_b_zero a 0
  have h1 := hopf_hasDerivAt_b_one a 0
  have h00 : deriv (fun s => hopfU a s 0 * conj (hopfU a s 0)) 0 = _ :=
    (h0.mul h0.star).deriv
  have h01 : deriv (fun s => hopfU a s 0 * conj (hopfU a s 1)) 0 = _ :=
    (h0.mul h1.star).deriv
  have h10 : deriv (fun s => hopfU a s 1 * conj (hopfU a s 0)) 0 = _ :=
    (h1.mul h0.star).deriv
  have h11 : deriv (fun s => hopfU a s 1 * conj (hopfU a s 1)) 0 = _ :=
    (h1.mul h1.star).deriv
  ext i j
  fin_cases i <;> fin_cases j
  · change deriv (fun s => hopfU a s 0 * conj (hopfU a s 0)) 0 = _
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    rw [h00]
    simp [hopfU, hsin, hcos]
  · change deriv (fun s => hopfU a s 0 * conj (hopfU a s 1)) 0 = _
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    rw [h01]
    simp [hopfU, hsin, hcos, Complex.conj_ofNat]
    ring
  · change deriv (fun s => hopfU a s 1 * conj (hopfU a s 0)) 0 = _
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    rw [h10]
    simp [hopfU, hsin, hcos, Complex.conj_ofNat]
  · change deriv (fun s => hopfU a s 1 * conj (hopfU a s 1)) 0 = _
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    rw [h11]
    simp [hopfU, hsin, hcos, Complex.conj_ofNat]
    ring

lemma hopf_projector_complex_b_zero (a : ℝ) :
    Complex.I * Matrix.trace (proj (hopfU a 0) *
      (dPa hopfU a 0 * dPb hopfU a 0 - dPb hopfU a 0 * dPa hopfU a 0)) =
        ((-2 * Real.sin a * Real.cos a : ℝ) : ℂ) := by
  rw [hopf_dPa_b_zero, hopf_dPb_b_zero]
  have hsin : conj (Complex.sin (a : ℂ)) = Complex.sin (a : ℂ) := by
    rw [← Complex.ofReal_sin, Complex.conj_ofReal]
  have hcos : conj (Complex.cos (a : ℂ)) = Complex.cos (a : ℂ) := by
    rw [← Complex.ofReal_cos, Complex.conj_ofReal]
  have ht := Complex.sin_sq_add_cos_sq (a : ℂ)
  have hI : (Complex.I : ℂ) ^ 2 = -1 := by norm_num [pow_two, Complex.I_mul_I]
  simp [proj, hopfU, hsin, hcos, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  linear_combination (2 * Complex.I ^ 2 * Complex.cos (a : ℂ) * Complex.sin (a : ℂ) *
    (Complex.sin (a : ℂ) ^ 2 + Complex.cos (a : ℂ) ^ 2 + 1)) * ht +
    (2 * Complex.cos (a : ℂ) * Complex.sin (a : ℂ)) * hI

lemma hopf_projector_b_zero (a : ℝ) :
    (Complex.I * Matrix.trace (proj (hopfU a 0) *
      (dPa hopfU a 0 * dPb hopfU a 0 - dPb hopfU a 0 * dPa hopfU a 0))).re =
        -2 * Real.sin a * Real.cos a := by
  rw [hopf_projector_complex_b_zero]
  exact Complex.ofReal_re _

/-- A concrete non-vacuous instance of the repaired curvature identity. -/
theorem hopf_curvature_eq_projector_b_zero (a : ℝ) :
    curvature hopfU a 0 = (Complex.I * Matrix.trace (proj (hopfU a 0) *
      (dPa hopfU a 0 * dPb hopfU a 0 - dPb hopfU a 0 * dPa hopfU a 0))).re := by
  rw [hopf_curvature, hopf_projector_b_zero]

lemma hopf_projector_pi_div_four :
    (Complex.I * Matrix.trace (proj (hopfU (Real.pi / 4) 0) *
      (dPa hopfU (Real.pi / 4) 0 * dPb hopfU (Real.pi / 4) 0 -
        dPb hopfU (Real.pi / 4) 0 * dPa hopfU (Real.pi / 4) 0))).re = -1 := by
  rw [← hopf_curvature_eq_projector_b_zero, hopf_curvature_pi_div_four]

theorem hopf_nonzero_benchmark :
    curvature hopfU (Real.pi / 4) 0 = -1 ∧
    (Complex.I * Matrix.trace (proj (hopfU (Real.pi / 4) 0) *
      (dPa hopfU (Real.pi / 4) 0 * dPb hopfU (Real.pi / 4) 0 -
        dPb hopfU (Real.pi / 4) 0 * dPa hopfU (Real.pi / 4) 0))).re = -1 := by
  exact ⟨hopf_curvature_pi_div_four, hopf_projector_pi_div_four⟩




end GaugeBenchmark
