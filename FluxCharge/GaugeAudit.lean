import Mathlib

/-!
# `FluxCharge.GaugeAudit` — mixed-partial symmetry is a necessary hypothesis

Companion to `FluxCharge.Gauge`. For `f = ab(a² − b²)/(a² + b²)` and the unit-normalised-at-the-origin
spinor `u = (1 + i f, 0)`, the mixed second partials of `f` at the origin are `-1` and `+1`; the
curvature is then `-2` while `i Tr(P [d_a P, d_b P])` is `0`. Unit norm at the point and both
differentiated-norm hypotheses hold, so the missing hypothesis is mixed symmetry and nothing weaker.

This is the Peano pathology used where it decides a statement rather than illustrating one.
-/

open scoped ComplexConjugate
open Complex Matrix

noncomputable section

namespace GaugeAudit


/-- The classic function with unequal mixed second partial derivatives at zero. -/
noncomputable def f (a b : ℝ) : ℝ := a * b * (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2)

lemma f_zero_left (b : ℝ) : f 0 b = 0 := by simp [f]
lemma f_zero_right (a : ℝ) : f a 0 = 0 := by simp [f]

lemma hasDerivAt_f_second (a : ℝ) : HasDerivAt (fun t => f a t) a 0 := by
  by_cases ha : a = 0
  · subst a
    simpa [f_zero_left] using (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ))
  · have h₁ : HasDerivAt (fun t : ℝ => a * t) a 0 := by
      convert (hasDerivAt_id (0 : ℝ)).const_mul a using 1
      · rfl
      · ring
    have h₂ : HasDerivAt (fun t : ℝ => a ^ 2 - t ^ 2) 0 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) (a ^ 2)).sub
        ((hasDerivAt_id (0 : ℝ)).pow 2) using 1
      · funext t
        rfl
      · simp [id]
    have h₃ : HasDerivAt (fun t : ℝ => a ^ 2 + t ^ 2) 0 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) (a ^ 2)).add
        ((hasDerivAt_id (0 : ℝ)).pow 2) using 1
      · funext t
        rfl
      · simp [id]
    have hne : a ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by positivity
    convert (h₁.mul h₂).div h₃ hne using 1
    · rfl
    · dsimp
      field_simp
      ring

lemma hasDerivAt_f_first (b : ℝ) : HasDerivAt (fun s => f s b) (-b) 0 := by
  have h := (hasDerivAt_f_second b).neg
  convert h using 1
  · funext s
    dsimp [f]
    rw [add_comm (b ^ 2) (s ^ 2)]
    ring

/-- The counterexample spinor. It equals `(1,0)` on both coordinate axes. -/
noncomputable def u (a b : ℝ) : Fin 2 → ℂ := ![1 + I * (f a b : ℂ), 0]

noncomputable def A1 (a b : ℝ) : ℝ :=
  (I * ((starRingEnd ℂ) (u a b 0) * deriv (fun s => u s b 0) a +
    (starRingEnd ℂ) (u a b 1) * deriv (fun s => u s b 1) a)).re

noncomputable def A2 (a b : ℝ) : ℝ :=
  (I * ((starRingEnd ℂ) (u a b 0) * deriv (fun t => u a t 0) b +
    (starRingEnd ℂ) (u a b 1) * deriv (fun t => u a t 1) b)).re

lemma u_axis (a : ℝ) : u a 0 = ![1, 0] := by
  funext i
  fin_cases i <;> simp [u, f_zero_right]

lemma u_axis' (b : ℝ) : u 0 b = ![1, 0] := by
  funext i
  fin_cases i <;> simp [u, f_zero_left]

lemma hasDerivAt_u_second (a : ℝ) :
    HasDerivAt (fun t => u a t 0) (I * (a : ℂ)) 0 := by
  simpa [u] using ((hasDerivAt_f_second a).ofReal_comp.const_mul I).const_add 1

lemma hasDerivAt_u_first (b : ℝ) :
    HasDerivAt (fun s => u s b 0) (I * (-b : ℂ)) 0 := by
  simpa [u] using ((hasDerivAt_f_first b).ofReal_comp.const_mul I).const_add 1

lemma A2_axis (a : ℝ) : A2 a 0 = -a := by
  have hd := (hasDerivAt_f_second a).ofReal_comp.deriv
  simp [A2, u, f_zero_right, hd]

lemma A1_axis (b : ℝ) : A1 0 b = b := by
  have hd := (hasDerivAt_f_first b).ofReal_comp.deriv
  simp [A1, u, f_zero_left, hd]

lemma curvature_at_zero :
    deriv (fun a => A2 a 0) 0 - deriv (fun b => A1 0 b) 0 = -2 := by
  have h2 : (fun a => A2 a 0) = fun a => -a := by funext a; exact A2_axis a
  have h1 : (fun b => A1 0 b) = fun b => b := by funext b; exact A1_axis b
  rw [h2, h1]
  norm_num

/-- The rank-one projector in the literal entrywise form requested in the audit. -/
noncomputable def P (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u a b 0 * (starRingEnd ℂ) (u a b 0),
      u a b 0 * (starRingEnd ℂ) (u a b 1);
     u a b 1 * (starRingEnd ℂ) (u a b 0),
      u a b 1 * (starRingEnd ℂ) (u a b 1)]

/-- Entrywise `deriv` of the projector in the first parameter. -/
noncomputable def D1 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  of fun i j => deriv (fun s => P s b i j) a

/-- Entrywise `deriv` of the projector in the second parameter. -/
noncomputable def D2 (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  of fun i j => deriv (fun t => P a t i j) b

noncomputable def F (a b : ℝ) : ℝ :=
  deriv (fun s => A2 s b) a - deriv (fun t => A1 a t) b

/-- The headline identity, with the necessary explicit real-to-complex coercion. -/
def headline (a b : ℝ) : Prop :=
  (F a b : ℂ) = I * trace (P a b * (D1 a b * D2 a b - D2 a b * D1 a b))

lemma unit_norm_at_zero :
    (starRingEnd ℂ) (u 0 0 0) * u 0 0 0 +
      (starRingEnd ℂ) (u 0 0 1) * u 0 0 1 = 1 := by
  rw [u_axis]
  norm_num

lemma first_tangency_at_zero :
    ((starRingEnd ℂ) (u 0 0 0) * deriv (fun s => u s 0 0) 0 +
      (starRingEnd ℂ) (u 0 0 1) * deriv (fun s => u s 0 1) 0).re = 0 := by
  simp [u_axis]

lemma second_tangency_at_zero :
    ((starRingEnd ℂ) (u 0 0 0) * deriv (fun t => u 0 t 0) 0 +
      (starRingEnd ℂ) (u 0 0 1) * deriv (fun t => u 0 t 1) 0).re = 0 := by
  simp [u_axis']

lemma D1_zero : D1 0 0 = 0 := by
  ext i j
  change deriv (fun s => P s 0 i j) 0 = 0
  have h : (fun s => P s 0 i j) = fun _ => P 0 0 i j := by
    funext s
    simp only [P, u_axis]
  rw [h]
  exact deriv_const _ _

lemma D2_zero : D2 0 0 = 0 := by
  ext i j
  change deriv (fun t => P 0 t i j) 0 = 0
  have h : (fun t => P 0 t i j) = fun _ => P 0 0 i j := by
    funext t
    simp only [P, u_axis']
  rw [h]
  exact deriv_const _ _

/-- Pointwise unit norm and both first-order tangency conditions do not suffice. -/
theorem pointwise_hypotheses_do_not_imply_headline :
    ((starRingEnd ℂ) (u 0 0 0) * u 0 0 0 +
        (starRingEnd ℂ) (u 0 0 1) * u 0 0 1 = 1) ∧
      (((starRingEnd ℂ) (u 0 0 0) * deriv (fun s => u s 0 0) 0 +
        (starRingEnd ℂ) (u 0 0 1) * deriv (fun s => u s 0 1) 0).re = 0) ∧
      (((starRingEnd ℂ) (u 0 0 0) * deriv (fun t => u 0 t 0) 0 +
        (starRingEnd ℂ) (u 0 0 1) * deriv (fun t => u 0 t 1) 0).re = 0) ∧
      ¬ headline 0 0 := by
  refine ⟨unit_norm_at_zero, first_tangency_at_zero, second_tangency_at_zero, ?_⟩
  have hF : F 0 0 = -2 := by
    exact curvature_at_zero
  simp only [headline, hF, D1_zero, D2_zero, mul_zero, sub_self, Matrix.trace_zero,
    mul_zero]
  norm_num


lemma norm_derivative_first_at_zero :
    deriv (fun s => (starRingEnd ℂ) (u s 0 0) * u s 0 0 +
      (starRingEnd ℂ) (u s 0 1) * u s 0 1) 0 = 0 := by
  have h : (fun s => (starRingEnd ℂ) (u s 0 0) * u s 0 0 +
      (starRingEnd ℂ) (u s 0 1) * u s 0 1) = fun _ => (1 : ℂ) := by
    funext s
    rw [u_axis]
    norm_num
  rw [h]
  exact deriv_const _ _

lemma norm_derivative_second_at_zero :
    deriv (fun t => (starRingEnd ℂ) (u 0 t 0) * u 0 t 0 +
      (starRingEnd ℂ) (u 0 t 1) * u 0 t 1) 0 = 0 := by
  have h : (fun t => (starRingEnd ℂ) (u 0 t 0) * u 0 t 0 +
      (starRingEnd ℂ) (u 0 t 1) * u 0 t 1) = fun _ => (1 : ℂ) := by
    funext t
    rw [u_axis']
    norm_num
  rw [h]
  exact deriv_const _ _

/-- Even the literal differentiated-norm hypotheses at the evaluation point,
without a common mixed second derivative, leave the headline identity false. -/
theorem derivative_norm_hypotheses_without_mixed_symmetry_do_not_imply_headline :
    ((starRingEnd ℂ) (u 0 0 0) * u 0 0 0 +
        (starRingEnd ℂ) (u 0 0 1) * u 0 0 1 = 1) ∧
      (deriv (fun s => (starRingEnd ℂ) (u s 0 0) * u s 0 0 +
        (starRingEnd ℂ) (u s 0 1) * u s 0 1) 0 = 0) ∧
      (deriv (fun t => (starRingEnd ℂ) (u 0 t 0) * u 0 t 0 +
        (starRingEnd ℂ) (u 0 t 1) * u 0 t 1) 0 = 0) ∧
      ¬ headline 0 0 := by
  refine ⟨unit_norm_at_zero, norm_derivative_first_at_zero,
    norm_derivative_second_at_zero, ?_⟩
  exact pointwise_hypotheses_do_not_imply_headline.2.2.2



end GaugeAudit
