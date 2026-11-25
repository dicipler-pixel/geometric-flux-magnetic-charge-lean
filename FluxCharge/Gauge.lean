import Mathlib

/-!
# `FluxCharge.Gauge` — the curvature of the Berry connection is the projector curvature

The gap this closes. `FluxCharge.Bundle` computes the connection coefficients of the two chart
sections and shows the curvature of that connection equals `sin θ / 2`; `FluxCharge.Monopole`
computes `i Tr(P [d_a P, d_b P])` from the projector. Neither proves, for a general family of unit
spinors, that the two are the *same* number. That identity is proved here, with its gauge law.

Two companions carry the evidence rather than the theorem: `FluxCharge.GaugeBenchmark` exhibits a
family where both sides are computed exactly and agree at a nonzero value, and drops each hypothesis
in turn to show the identity fails; `FluxCharge.GaugeAudit` isolates the mixed-partial obstruction.

Conventions: `A_a = Re(i ⟨u, d_a u⟩)` with `⟨x,y⟩ = conj x₀ y₀ + conj x₁ y₁`, and
`F = d_a A_b − d_b A_a`; the projector is `P = u u†`.

Provenance: an eight-member two-sided proof audit. A breaker side attacked every statement, the
sides then swapped roles, and this statement was repaired four times before it survived: the gauge
law is minus the gradient and not plus, tangency and mixed-partial symmetry both turned out to be
necessary, and the real-to-complex coercion had to be stated.

Mathlib only: nothing here depends on the monopole chain.
-/

open scoped ComplexConjugate BigOperators
open Matrix

noncomputable section

namespace Berry


/-- The rank-one projector associated with a two-component spinor. -/
def P (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u a b 0 * conj (u a b 0), u a b 0 * conj (u a b 1);
     u a b 1 * conj (u a b 0), u a b 1 * conj (u a b 1)]

lemma P_conjTranspose (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) :
    (P u a b)ᴴ = P u a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P, Matrix.conjTranspose_apply] <;> ring

lemma P_mul_self (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (hu : conj (u a b 0) * u a b 0 + conj (u a b 1) * u a b 1 = 1) :
    P u a b * P u a b = P u a b := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [P, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (u a b 0 * conj (u a b 0)) * hu
  · simp [P, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (u a b 0 * conj (u a b 1)) * hu
  · simp [P, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (u a b 1 * conj (u a b 0)) * hu
  · simp [P, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (u a b 1 * conj (u a b 1)) * hu

lemma P_trace (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (hu : conj (u a b 0) * u a b 0 + conj (u a b 1) * u a b 1 = 1) :
    Matrix.trace (P u a b) = 1 := by
  simpa [P, Matrix.trace, Fin.sum_univ_two, mul_comm] using hu

/-- Entrywise derivative of the projector in the first parameter. -/
lemma P_deriv_apply (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (hu : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a) (i j : Fin 2) :
    deriv (fun s => P u s b i j) a =
      deriv (fun s => u s b i) a * conj (u a b j) +
        u a b i * conj (deriv (fun s => u s b j) a) := by
  fin_cases i <;> fin_cases j
  · change deriv ((fun s => u s b 0) * (fun s => conj (u s b 0))) a = _
    exact ((hu 0).hasDerivAt.mul (hu 0).hasDerivAt.star).deriv
  · change deriv ((fun s => u s b 0) * (fun s => conj (u s b 1))) a = _
    exact ((hu 0).hasDerivAt.mul (hu 1).hasDerivAt.star).deriv
  · change deriv ((fun s => u s b 1) * (fun s => conj (u s b 0))) a = _
    exact ((hu 1).hasDerivAt.mul (hu 0).hasDerivAt.star).deriv
  · change deriv ((fun s => u s b 1) * (fun s => conj (u s b 1))) a = _
    exact ((hu 1).hasDerivAt.mul (hu 1).hasDerivAt.star).deriv

/-- Differentiation commutes with taking the real part (over `ℝ`). -/
lemma hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {a : ℝ}
    (h : HasDerivAt f f' a) : HasDerivAt (fun s => (f s).re) f'.re a := by
  convert Complex.reCLM.hasFDerivAt.comp_hasDerivAt a h using 1 <;>
    simp [Function.comp_def]

/-- Real tangency obtained by differentiating the unit-norm constraint. -/
lemma tangency (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (hu : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a)
    (hnorm : deriv (fun s => conj (u s b 0) * u s b 0 +
      conj (u s b 1) * u s b 1) a = 0) :
    (conj (u a b 0) * deriv (fun s => u s b 0) a +
      conj (u a b 1) * deriv (fun s => u s b 1) a).re = 0 := by
  have hd := (((hu 0).hasDerivAt.star.mul (hu 0).hasDerivAt).add
    ((hu 1).hasDerivAt.star.mul (hu 1).hasDerivAt)).deriv
  have hd' : deriv (fun s => conj (u s b 0) * u s b 0 +
      conj (u s b 1) * u s b 1) a =
      conj (deriv (fun s => u s b 0) a) * u a b 0 +
        conj (u a b 0) * deriv (fun s => u s b 0) a +
      (conj (deriv (fun s => u s b 1) a) * u a b 1 +
        conj (u a b 1) * deriv (fun s => u s b 1) a) := hd
  rw [hd'] at hnorm
  have hr := congrArg Complex.re hnorm
  simp [Complex.mul_re] at hr ⊢
  ring_nf at hr ⊢
  linarith

/-- Berry's complex inner product before taking the real part. -/
def B (f g : Fin 2 → ℂ) : ℂ :=
  Complex.I * (conj (f 0) * g 0 + conj (f 1) * g 1)

/-- Berry connection of a one-parameter family and a specified derivative family. -/
def connRe (f g : ℝ → (Fin 2 → ℂ)) (s : ℝ) : ℝ := (B (f s) (g s)).re

/-- The actual real Berry connection of a one-parameter family. -/
def A (f : ℝ → (Fin 2 → ℂ)) (s : ℝ) : ℝ :=
  connRe f (fun x => fun i => deriv (fun t => f t i) x) s

/-- First-parameter Berry connection. -/
def A₁ (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) : ℝ :=
  A (fun s => u s b) a

/-- Second-parameter Berry connection. -/
def A₂ (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) : ℝ :=
  A (fun t => u a t) b

lemma hasDerivAt_connRe (f g : ℝ → (Fin 2 → ℂ)) (a : ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (fun s => f s i) a)
    (hg : ∀ i, DifferentiableAt ℝ (fun s => g s i) a) :
    HasDerivAt (connRe f g)
      (Complex.I * ((conj (deriv (fun s => f s 0) a) * g a 0 +
          conj (f a 0) * deriv (fun s => g s 0) a) +
        (conj (deriv (fun s => f s 1) a) * g a 1 +
          conj (f a 1) * deriv (fun s => g s 1) a))).re a := by
  apply hasDerivAt_re
  simpa [B, Pi.add_apply, Pi.mul_apply] using! HasDerivAt.mul (𝕜 := ℝ) (hasDerivAt_const (𝕜 := ℝ) a Complex.I)
    ((HasDerivAt.mul (𝕜 := ℝ) (hf 0).hasDerivAt.star (hg 0).hasDerivAt).add
      (HasDerivAt.mul (𝕜 := ℝ) (hf 1).hasDerivAt.star (hg 1).hasDerivAt))

/-- Curvature of the two real connections. -/
def F (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) : ℝ :=
  deriv (fun s => A₂ u s b) a - deriv (fun t => A₁ u a t) b

/-- Entrywise matrix derivative. -/
def dP (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i j => deriv (fun x => M x i j) s



/-- The two first-parameter derivative components. -/
def du₁ (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) (i : Fin 2) : ℂ :=
  deriv (fun s => u s b i) a

/-- The two second-parameter derivative components. -/
def du₂ (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) (i : Fin 2) : ℂ :=
  deriv (fun t => u a t i) b

/-- The projector derivative in the first parameter, as an explicit matrix. -/
def dP₁ (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  dP (fun s => P u s b) a

/-- The projector derivative in the second parameter, as an explicit matrix. -/
def dP₂ (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  dP (fun t => P u a t) b

/-- The complex matrix form of the headline identity. -/
def projectorCurvature (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) : ℂ :=
  Complex.I * Matrix.trace (P u a b * (dP₁ u a b * dP₂ u a b - dP₂ u a b * dP₁ u a b))


/-- A rank-one matrix, written without matrix notation for algebraic calculations. -/
def outer (u v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => u i * conj (v j)

/-- The two-component Hermitian inner product, linear in the second argument. -/
def dot (u v : Fin 2 → ℂ) : ℂ := conj (u 0) * v 0 + conj (u 1) * v 1

lemma outer_mul_outer (u v w z : Fin 2 → ℂ) :
    outer u v * outer w z = dot v w • outer u z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [outer, dot, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;> ring

lemma trace_outer (u v : Fin 2 → ℂ) :
    Matrix.trace (outer u v) = dot v u := by
  simp [outer, dot, Matrix.trace, Fin.sum_univ_two, mul_comm]

lemma dot_conj (u v : Fin 2 → ℂ) : dot u v = conj (dot v u) := by
  simp [dot, map_add, mul_comm]

lemma conj_eq_neg_of_re_eq_zero {z : ℂ} (hz : z.re = 0) : conj z = -z := by
  apply Complex.ext
  · simp only [Complex.conj_re, Complex.neg_re]
    linarith
  · simp

lemma trace_projector_commutator (u p q : Fin 2 → ℂ)
    (hnorm : dot u u = 1) (hp : (dot u p).re = 0) (hq : (dot u q).re = 0) :
    Matrix.trace (outer u u *
      ((outer p u + outer u p) * (outer q u + outer u q) -
       (outer q u + outer u q) * (outer p u + outer u p))) =
      dot p q - dot q p := by
  have hpc : dot p u = -dot u p := by
    rw [dot_conj, conj_eq_neg_of_re_eq_zero hp]
  have hqc : dot q u = -dot u q := by
    rw [dot_conj, conj_eq_neg_of_re_eq_zero hq]
  simp only [add_mul, mul_add, outer_mul_outer, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, trace_outer,
    smul_add, add_smul, Matrix.mul_smul]
  rw [hnorm, hpc, hqc]
  ring


lemma berry_re_sub (z w : ℂ) :
    (Complex.I * (z + w)).re - (Complex.I * (conj z + w)).re = -2 * z.im := by
  simp [Complex.mul_re]
  ring

/-- Connection calculus reduces curvature to the imaginary part of `p†q`.
The two derivative hypotheses explicitly carry the common mixed second derivative. -/
lemma F_eq_im_of_hasDerivAt (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (r : Fin 2 → ℂ)
    (h₂ : HasDerivAt (fun s => A₂ u s b)
      (Complex.I * (dot (du₁ u a b) (du₂ u a b) + dot (u a b) r)).re a)
    (h₁ : HasDerivAt (fun t => A₁ u a t)
      (Complex.I * (dot (du₂ u a b) (du₁ u a b) + dot (u a b) r)).re b) :
    F u a b = -2 * (dot (du₁ u a b) (du₂ u a b)).im := by
  rw [F, h₂.deriv, h₁.deriv, dot_conj (du₂ u a b) (du₁ u a b)]
  exact berry_re_sub _ _


lemma P_eq_outer (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) :
    P u a b = outer (u a b) (u a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma P_deriv_apply_second (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (hu : ∀ k, DifferentiableAt ℝ (fun t => u a t k) b) (i j : Fin 2) :
    deriv (fun t => P u a t i j) b =
      deriv (fun t => u a t i) b * conj (u a b j) +
        u a b i * conj (deriv (fun t => u a t j) b) := by
  fin_cases i <;> fin_cases j <;>
    simpa [P, Pi.mul_apply] using! ((hu _).hasDerivAt.mul (hu _).hasDerivAt.star).deriv

lemma dP₁_eq_outer (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (hu : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a) :
    dP₁ u a b = outer (du₁ u a b) (u a b) + outer (u a b) (du₁ u a b) := by
  ext i j
  exact P_deriv_apply u a b hu i j

lemma dP₂_eq_outer (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (hu : ∀ k, DifferentiableAt ℝ (fun t => u a t k) b) :
    dP₂ u a b = outer (du₂ u a b) (u a b) + outer (u a b) (du₂ u a b) := by
  ext i j
  exact P_deriv_apply_second u a b hu i j

lemma I_mul_sub_conj (z : ℂ) :
    Complex.I * (z - conj z) = ((-2 * z.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Headline theorem in a fully exposed analytic form.  The two connection
derivatives share the mixed second derivative `r`; all remaining hypotheses
are the literal pointwise unit-norm and real-tangency conditions. -/
lemma curvature_eq_projector_of_hasDerivAt
    (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) (r : Fin 2 → ℂ)
    (hu₁ : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a)
    (hu₂ : ∀ k, DifferentiableAt ℝ (fun t => u a t k) b)
    (hnorm : dot (u a b) (u a b) = 1)
    (htan₁ : (dot (u a b) (du₁ u a b)).re = 0)
    (htan₂ : (dot (u a b) (du₂ u a b)).re = 0)
    (h₂ : HasDerivAt (fun s => A₂ u s b)
      (Complex.I * (dot (du₁ u a b) (du₂ u a b) + dot (u a b) r)).re a)
    (h₁ : HasDerivAt (fun t => A₁ u a t)
      (Complex.I * (dot (du₂ u a b) (du₁ u a b) + dot (u a b) r)).re b) :
    (F u a b : ℂ) = projectorCurvature u a b := by
  have hF := F_eq_im_of_hasDerivAt u a b r h₂ h₁
  have htr := trace_projector_commutator (u a b) (du₁ u a b) (du₂ u a b)
    hnorm htan₁ htan₂
  rw [hF]
  unfold projectorCurvature
  rw [P_eq_outer, dP₁_eq_outer u a b hu₁, dP₂_eq_outer u a b hu₂, htr,
    dot_conj (du₂ u a b) (du₁ u a b), I_mul_sub_conj]


lemma A₂_eq_connRe (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) :
    A₂ u a b = connRe (fun s => u s b) (fun s => du₂ u s b) a := rfl

lemma A₁_eq_connRe (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) :
    A₁ u a b = connRe (fun t => u a t) (fun t => du₁ u a t) b := rfl

lemma hasDerivAt_A₂_of_mixed (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (r : Fin 2 → ℂ)
    (hu : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a)
    (hr : ∀ k, HasDerivAt (fun s => du₂ u s b k) (r k) a) :
    HasDerivAt (fun s => A₂ u s b)
      (Complex.I * (dot (du₁ u a b) (du₂ u a b) + dot (u a b) r)).re a := by
  have h := hasDerivAt_connRe (fun s => u s b) (fun s => du₂ u s b) a hu
    (fun k => (hr k).differentiableAt)
  rw [(hr 0).deriv, (hr 1).deriv] at h
  convert h using 1
  · funext s
    exact A₂_eq_connRe u s b
  · congr 1
    simp only [du₁, dot]
    ring

lemma hasDerivAt_A₁_of_mixed (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (r : Fin 2 → ℂ)
    (hu : ∀ k, DifferentiableAt ℝ (fun t => u a t k) b)
    (hr : ∀ k, HasDerivAt (fun t => du₁ u a t k) (r k) b) :
    HasDerivAt (fun t => A₁ u a t)
      (Complex.I * (dot (du₂ u a b) (du₁ u a b) + dot (u a b) r)).re b := by
  have h := hasDerivAt_connRe (fun t => u a t) (fun t => du₁ u a t) b hu
    (fun k => (hr k).differentiableAt)
  rw [(hr 0).deriv, (hr 1).deriv] at h
  convert h using 1
  · funext t
    exact A₁_eq_connRe u a t
  · congr 1
    simp only [du₂, dot]
    ring


/-- Repaired headline theorem.  The arguments `hr₂` and `hr₁` say that the
two mixed second partial derivatives exist and are equal to the same `r`. -/
lemma curvature_eq_projector
    (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) (r : Fin 2 → ℂ)
    (hu₁ : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a)
    (hu₂ : ∀ k, DifferentiableAt ℝ (fun t => u a t k) b)
    (hr₂ : ∀ k, HasDerivAt (fun s => du₂ u s b k) (r k) a)
    (hr₁ : ∀ k, HasDerivAt (fun t => du₁ u a t k) (r k) b)
    (hnorm : dot (u a b) (u a b) = 1)
    (htan₁ : (dot (u a b) (du₁ u a b)).re = 0)
    (htan₂ : (dot (u a b) (du₂ u a b)).re = 0) :
    (F u a b : ℂ) = projectorCurvature u a b := by
  exact curvature_eq_projector_of_hasDerivAt u a b r hu₁ hu₂ hnorm htan₁ htan₂
    (hasDerivAt_A₂_of_mixed u a b r hu₁ hr₂)
    (hasDerivAt_A₁_of_mixed u a b r hu₂ hr₁)


lemma tangency_left_of_unit (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (hu : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a)
    (hunit : ∀ s t, dot (u s t) (u s t) = 1) :
    (dot (u a b) (du₁ u a b)).re = 0 := by
  have hnorm : deriv (fun s => conj (u s b 0) * u s b 0 +
      conj (u s b 1) * u s b 1) a = 0 := by
    have hfun : (fun s => conj (u s b 0) * u s b 0 +
        conj (u s b 1) * u s b 1) = (fun _ => (1 : ℂ)) := by
      funext s
      exact hunit s b
    rw [hfun, deriv_const]
  simpa [dot, du₁] using tangency u a b hu hnorm

lemma tangency_right_of_unit (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ)
    (hu : ∀ k, DifferentiableAt ℝ (fun t => u a t k) b)
    (hunit : ∀ s t, dot (u s t) (u s t) = 1) :
    (dot (u a b) (du₂ u a b)).re = 0 := by
  have hnorm : deriv (fun t => conj (u a t 0) * u a t 0 +
      conj (u a t 1) * u a t 1) b = 0 := by
    have hfun : (fun t => conj (u a t 0) * u a t 0 +
        conj (u a t 1) * u a t 1) = (fun _ => (1 : ℂ)) := by
      funext t
      exact hunit a t
    rw [hfun, deriv_const]
  simpa [dot, du₂] using tangency (fun s t => u t s) b a hu hnorm

/-- Unit-norm version of the headline, with the mixed derivatives exposed. -/
lemma curvature_eq_projector_unit
    (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) (r : Fin 2 → ℂ)
    (hu₁ : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a)
    (hu₂ : ∀ k, DifferentiableAt ℝ (fun t => u a t k) b)
    (hr₂ : ∀ k, HasDerivAt (fun s => du₂ u s b k) (r k) a)
    (hr₁ : ∀ k, HasDerivAt (fun t => du₁ u a t k) (r k) b)
    (hunit : ∀ s t, dot (u s t) (u s t) = 1) :
    (F u a b : ℂ) = projectorCurvature u a b := by
  exact curvature_eq_projector u a b r hu₁ hu₂ hr₂ hr₁ (hunit a b)
    (tangency_left_of_unit u a b hu₁ hunit)
    (tangency_right_of_unit u a b hu₂ hunit)

lemma hasDerivAt_left_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : Differentiable ℝ f) (a b : ℝ) :
    HasDerivAt (fun s => f (s, b)) (fderiv ℝ f (a, b) (1, 0)) a := by
  have hline : HasDerivAt (fun s : ℝ => (s, b)) (1, 0) a :=
    (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  simpa only [Function.comp_apply] using! (hf (a, b)).hasFDerivAt.comp_hasDerivAt a hline

lemma hasDerivAt_right_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : Differentiable ℝ f) (a b : ℝ) :
    HasDerivAt (fun t => f (a, t)) (fderiv ℝ f (a, b) (0, 1)) b := by
  have hline : HasDerivAt (fun t : ℝ => (a, t)) (0, 1) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  simpa only [Function.comp_apply] using! (hf (a, b)).hasFDerivAt.comp_hasDerivAt b hline

lemma hasDerivAt_left_of_right_fderiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    HasDerivAt (fun s => fderiv ℝ f (s, b) (0, 1))
      (fderiv ℝ (fderiv ℝ f) (a, b) (1, 0) (0, 1)) a := by
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (a, b)) (a, b) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (a, b)).hasFDerivAt
  have heval := (ContinuousLinearMap.apply ℝ F ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp (a, b) hD
  have hline : HasDerivAt (fun s : ℝ => (s, b)) (1, 0) a :=
    (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  have h := heval.comp_hasDerivAt a hline
  simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply] using! h

lemma hasDerivAt_right_of_left_fderiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    HasDerivAt (fun t => fderiv ℝ f (a, t) (1, 0))
      (fderiv ℝ (fderiv ℝ f) (a, b) (0, 1) (1, 0)) b := by
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (a, b)) (a, b) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (a, b)).hasFDerivAt
  have heval := (ContinuousLinearMap.apply ℝ F ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp (a, b) hD
  have hline : HasDerivAt (fun t : ℝ => (a, t)) (0, 1) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have h := heval.comp_hasDerivAt b hline
  simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply] using! h


lemma deriv_mixed_of_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F}
    (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    deriv (fun s => deriv (fun t => f (s, t)) b) a =
      deriv (fun t => deriv (fun s => f (s, t)) a) b := by
  have hfl := hasDerivAt_left_slice (hf.differentiable (by norm_num))
  have hfr := hasDerivAt_right_slice (hf.differentiable (by norm_num))
  have heq_b (s : ℝ) : deriv (fun t => f (s, t)) b = fderiv ℝ f (s, b) (0, 1) :=
    (hfr s b).deriv
  have heq_a (t : ℝ) : deriv (fun s => f (s, t)) a = fderiv ℝ f (a, t) (1, 0) :=
    (hfl a t).deriv
  simp_rw [heq_b, heq_a]
  rw [(hasDerivAt_left_of_right_fderiv hf a b).deriv,
    (hasDerivAt_right_of_left_fderiv hf a b).deriv]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq (1, 0) (0, 1)




lemma hasDerivAt_left_of_right_deriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    HasDerivAt (fun s => deriv (fun t => f (s, t)) b)
      (fderiv ℝ (fderiv ℝ f) (a, b) (1, 0) (0, 1)) a := by
  have heq : (fun s => deriv (fun t => f (s, t)) b) =
      (fun s => fderiv ℝ f (s, b) (0, 1)) := by
    funext s
    exact (hasDerivAt_right_slice (hf.differentiable (by norm_num)) s b).deriv
  rw [heq]
  exact hasDerivAt_left_of_right_fderiv hf a b

lemma hasDerivAt_right_of_left_deriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    HasDerivAt (fun t => deriv (fun s => f (s, t)) a)
      (fderiv ℝ (fderiv ℝ f) (a, b) (0, 1) (1, 0)) b := by
  have heq : (fun t => deriv (fun s => f (s, t)) a) =
      (fun t => fderiv ℝ f (a, t) (1, 0)) := by
    funext t
    exact (hasDerivAt_left_slice (hf.differentiable (by norm_num)) a t).deriv
  rw [heq]
  exact hasDerivAt_right_of_left_fderiv hf a b


lemma differentiableAt_left_of_right_deriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ × ℝ → F} (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    DifferentiableAt ℝ (fun s => deriv (fun t => f (s, t)) b) a :=
  (hasDerivAt_left_of_right_deriv hf a b).differentiableAt

lemma differentiableAt_right_of_left_deriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ × ℝ → F} (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    DifferentiableAt ℝ (fun t => deriv (fun s => f (s, t)) a) b :=
  (hasDerivAt_right_of_left_deriv hf a b).differentiableAt

lemma second_derivative_data_of_contDiff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → ℝ → F} (hf : ContDiff ℝ 2 (Function.uncurry f))
    (a b : ℝ) :
    DifferentiableAt ℝ (fun s => f s b) a ∧
    DifferentiableAt ℝ (fun t => f a t) b ∧
    DifferentiableAt ℝ (fun s => deriv (fun t => f s t) b) a ∧
    DifferentiableAt ℝ (fun t => deriv (fun s => f s t) a) b ∧
    deriv (fun s => deriv (fun t => f s t) b) a =
      deriv (fun t => deriv (fun s => f s t) a) b := by
  refine ⟨?_, ?_, differentiableAt_left_of_right_deriv hf a b,
    differentiableAt_right_of_left_deriv hf a b, deriv_mixed_of_contDiff hf a b⟩
  · exact (hasDerivAt_left_slice (hf.differentiable (by norm_num)) a b).differentiableAt
  · exact (hasDerivAt_right_slice (hf.differentiable (by norm_num)) a b).differentiableAt


/-- Smooth unit-family form of the headline theorem. -/
theorem curvature_eq_projector_contDiff
    (u : ℝ → ℝ → (Fin 2 → ℂ))
    (hu : ∀ k, ContDiff ℝ 2 (Function.uncurry (fun s t => u s t k)))
    (hunit : ∀ s t, dot (u s t) (u s t) = 1) (a b : ℝ) :
    (F u a b : ℂ) = projectorCurvature u a b := by
  let r : Fin 2 → ℂ := fun k => deriv (fun s => du₂ u s b k) a
  have hd (k : Fin 2) := second_derivative_data_of_contDiff (hu k) a b
  have hu₁ : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a := fun k => (hd k).1
  have hu₂ : ∀ k, DifferentiableAt ℝ (fun t => u a t k) b := fun k => (hd k).2.1
  have hr₂ : ∀ k, HasDerivAt (fun s => du₂ u s b k) (r k) a := by
    intro k
    simpa [r, du₂] using (hd k).2.2.1.hasDerivAt
  have hr₁ : ∀ k, HasDerivAt (fun t => du₁ u a t k) (r k) b := by
    intro k
    have h := (hd k).2.2.2.1.hasDerivAt
    have heq : r k = deriv (fun t => du₁ u a t k) b := by
      simpa [r, du₁, du₂] using (hd k).2.2.2.2
    rw [heq]
    simpa [du₁] using h
  exact curvature_eq_projector_unit u a b r hu₁ hu₂ hr₂ hr₁ hunit


/-- Componentwise multiplication by the specified gauge phase. -/
def gauge (lambda : ℝ → ℝ → ℝ) (u : ℝ → ℝ → (Fin 2 → ℂ))
    (a b : ℝ) : Fin 2 → ℂ :=
  fun i => Complex.exp (Complex.I * (lambda a b : ℂ)) * u a b i


lemma conj_phase_mul_phase (x : ℝ) :
    conj (Complex.exp (Complex.I * (x : ℂ))) * Complex.exp (Complex.I * (x : ℂ)) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

lemma hasDerivAt_gauge_phase {lambda : ℝ → ℝ} {x : ℝ}
    (h : DifferentiableAt ℝ lambda x) :
    HasDerivAt (fun s => Complex.exp (Complex.I * (lambda s : ℂ)))
      (Complex.exp (Complex.I * (lambda x : ℂ)) *
        (Complex.I * ((deriv lambda x : ℝ) : ℂ))) x := by
  have hr : HasDerivAt (fun s => (lambda s : ℂ)) ((deriv lambda x : ℝ) : ℂ) x :=
    h.hasDerivAt.ofReal_comp
  exact (hr.const_mul Complex.I).cexp

/--
The corrected connection gauge law. Differentiability is necessary to use `deriv`;
unit norm is needed only at the point where the connection is evaluated.
-/
lemma A_gauge_sub (u : ℝ → ℝ → (Fin 2 → ℂ)) (lambda : ℝ → ℝ → ℝ) (a b : ℝ)
    (hu : ∀ k, DifferentiableAt ℝ (fun s => u s b k) a)
    (hl : DifferentiableAt ℝ (fun s => lambda s b) a)
    (hnorm : conj (u a b 0) * u a b 0 + conj (u a b 1) * u a b 1 = 1) :
    A₁ (gauge lambda u) a b = A₁ u a b - deriv (fun s => lambda s b) a := by
  let z : ℂ := Complex.exp (Complex.I * (lambda a b : ℂ))
  let r : ℂ := ((deriv (fun s => lambda s b) a : ℝ) : ℂ)
  have hz : HasDerivAt (fun s => Complex.exp (Complex.I * (lambda s b : ℂ)))
      (z * (Complex.I * r)) a := hasDerivAt_gauge_phase hl
  have hd0 := hz.mul (hu 0).hasDerivAt
  have hd1 := hz.mul (hu 1).hasDerivAt
  have hd0' : deriv (fun s => gauge lambda u s b 0) a =
      z * (Complex.I * r) * u a b 0 + z * deriv (fun s => u s b 0) a := by
    exact hd0.deriv
  have hd1' : deriv (fun s => gauge lambda u s b 1) a =
      z * (Complex.I * r) * u a b 1 + z * deriv (fun s => u s b 1) a := by
    exact hd1.deriv
  have hzunit : conj z * z = 1 := conj_phase_mul_phase (lambda a b)
  have hcomplex :
      Complex.I * (conj (gauge lambda u a b 0) *
          (z * (Complex.I * r) * u a b 0 + z * deriv (fun s => u s b 0) a) +
        conj (gauge lambda u a b 1) *
          (z * (Complex.I * r) * u a b 1 + z * deriv (fun s => u s b 1) a)) =
      Complex.I * (conj (u a b 0) * deriv (fun s => u s b 0) a +
        conj (u a b 1) * deriv (fun s => u s b 1) a) - r := by
    simp only [gauge, map_mul]
    change Complex.I * (conj z * conj (u a b 0) *
          (z * (Complex.I * r) * u a b 0 + z * deriv (fun s => u s b 0) a) +
        conj z * conj (u a b 1) *
          (z * (Complex.I * r) * u a b 1 + z * deriv (fun s => u s b 1) a)) = _
    calc
      _ = (conj z * z) * (Complex.I * (conj (u a b 0) * deriv (fun s => u s b 0) a +
            conj (u a b 1) * deriv (fun s => u s b 1) a)) +
          (conj z * z) * (Complex.I * Complex.I * r *
            (conj (u a b 0) * u a b 0 + conj (u a b 1) * u a b 1)) := by ring
      _ = _ := by rw [hzunit, hnorm, Complex.I_mul_I]; ring
  unfold A₁ A connRe B
  simp only
  rw [hd0', hd1']
  rw [hcomplex]
  simp [r]


lemma conj_phase_mul_left (z x y : ℂ) (hz : conj z * z = 1) :
    conj (z * x) * (z * y) = conj x * y := by
  rw [map_mul]
  calc
    _ = (conj z * z) * (conj x * y) := by ring
    _ = _ := by rw [hz, one_mul]

lemma phase_mul_conj (z x y : ℂ) (hz : conj z * z = 1) :
    (z * x) * conj (z * y) = x * conj y := by
  rw [map_mul]
  calc
    _ = (conj z * z) * (x * conj y) := by ring
    _ = _ := by rw [hz, one_mul]

/-- Swap the two scalar parameters. -/
def flip {X : Type*} (u : ℝ → ℝ → X) : ℝ → ℝ → X :=
  fun a b => u b a

lemma flip_gauge (u : ℝ → ℝ → (Fin 2 → ℂ)) (lambda : ℝ → ℝ → ℝ) :
    flip (gauge lambda u) = gauge (flip lambda) (flip u) := by
  rfl


/-- Projector gauge invariance needs no norm or differentiability hypothesis. -/
theorem P_gauge (u : ℝ → ℝ → (Fin 2 → ℂ)) (lambda : ℝ → ℝ → ℝ) (a b : ℝ) :
    P (gauge lambda u) a b = P u a b := by
  have hz := conj_phase_mul_phase (lambda a b)
  ext i j
  fin_cases i <;> fin_cases j <;> apply phase_mul_conj _ _ _ hz



lemma curvature_sub_gradient_of_contDiff {B C : ℝ → ℝ → ℝ} {lam : ℝ → ℝ → ℝ}
    {a b : ℝ} (hC : DifferentiableAt ℝ (fun s => C s b) a)
    (hB : DifferentiableAt ℝ (fun t => B a t) b)
    (hlam : ContDiff ℝ 2 (Function.uncurry lam)) :
    deriv (fun s => C s b - deriv (fun t => lam s t) b) a -
      deriv (fun t => B a t - deriv (fun s => lam s t) a) b =
    deriv (fun s => C s b) a - deriv (fun t => B a t) b := by
  let f : ℝ × ℝ → ℝ := Function.uncurry lam
  have hba : HasDerivAt (fun s => deriv (fun t => lam s t) b)
      (fderiv ℝ (fderiv ℝ f) (a, b) (1, 0) (0, 1)) a :=
    hasDerivAt_left_of_right_deriv hlam a b
  have hab : HasDerivAt (fun t => deriv (fun s => lam s t) a)
      (fderiv ℝ (fderiv ℝ f) (a, b) (0, 1) (1, 0)) b :=
    hasDerivAt_right_of_left_deriv hlam a b
  have hsuba := (hC.hasDerivAt.sub hba).deriv
  have hsubb := (hB.hasDerivAt.sub hab).deriv
  change deriv (fun s => C s b - deriv (fun t => lam s t) b) a = _ at hsuba
  change deriv (fun t => B a t - deriv (fun s => lam s t) a) b = _ at hsubb
  rw [hsuba, hsubb]
  have hcont : ContDiffAt ℝ 2 f (a, b) := hlam.contDiffAt
  have hsymm : fderiv ℝ (fderiv ℝ f) (a, b) (1, 0) (0, 1) =
      fderiv ℝ (fderiv ℝ f) (a, b) (0, 1) (1, 0) :=
    (hcont.isSymmSndFDerivAt (by simp)).eq (1, 0) (0, 1)
  change deriv (fun s => C s b) a - _ - (deriv (fun t => B a t) b - _) = _
  rw [← hsymm]
  ring






/--
Curvature is gauge invariant once the derivative operations are valid. The plus-sign
connection law was false; the minus sign here comes from `A_gauge_sub`. Mixed
partial symmetry of lambda is why the two correction terms cancel.
-/
theorem F_gauge_of_contDiff (u : ℝ → ℝ → (Fin 2 → ℂ)) (lambda : ℝ → ℝ → ℝ) (a b : ℝ)
    (hunit : ∀ s t, conj (u s t 0) * u s t 0 + conj (u s t 1) * u s t 1 = 1)
    (hu1 : ∀ s t k, DifferentiableAt ℝ (fun x => u x t k) s)
    (hu2 : ∀ s t k, DifferentiableAt ℝ (fun x => u s x k) t)
    (hC : DifferentiableAt ℝ (fun s => A₂ u s b) a)
    (hB : DifferentiableAt ℝ (fun t => A₁ u a t) b)
    (hlam : ContDiff ℝ 2 (Function.uncurry lambda)) :
    F (gauge lambda u) a b = F u a b := by
  have hld : Differentiable ℝ (Function.uncurry lambda) := hlam.differentiable (by norm_num)
  have hl1 (s t : ℝ) : DifferentiableAt ℝ (fun x => lambda x t) s :=
    (hasDerivAt_left_slice hld s t).differentiableAt
  have hl2 (s t : ℝ) : DifferentiableAt ℝ (fun x => lambda s x) t :=
    (hasDerivAt_right_slice hld s t).differentiableAt
  have hs1 (s t : ℝ) : A₁ (gauge lambda u) s t = A₁ u s t -
      deriv (fun x => lambda x t) s :=
    A_gauge_sub u lambda s t (hu1 s t) (hl1 s t) (hunit s t)
  have hs2 (s t : ℝ) : A₂ (gauge lambda u) s t = A₂ u s t -
      deriv (fun x => lambda s x) t := by
    change A₁ (flip (gauge lambda u)) t s = A₁ (flip u) t s -
      deriv (fun x => lambda s x) t
    rw [flip_gauge]
    exact A_gauge_sub (flip u) (flip lambda) t s (hu2 s t) (hl2 s t) (hunit s t)
  unfold F
  rw [show (fun s => A₂ (gauge lambda u) s b) =
    (fun s => A₂ u s b - deriv (fun t => lambda s t) b) from
      funext (fun s => hs2 s b)]
  rw [show (fun t => A₁ (gauge lambda u) a t) =
    (fun t => A₁ u a t - deriv (fun s => lambda s t) a) from
      funext (fun t => hs1 a t)]
  exact curvature_sub_gradient_of_contDiff hC hB hlam




/-- The first connection is definitionally the literal formula in the target. -/
lemma A₁_eq_literal (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) :
    A₁ u a b = (Complex.I * (conj (u a b 0) * deriv (fun s => u s b 0) a +
      conj (u a b 1) * deriv (fun s => u s b 1) a)).re := rfl

/-- The second connection is the same literal formula along the second slice. -/
lemma A₂_eq_literal (u : ℝ → ℝ → (Fin 2 → ℂ)) (a b : ℝ) :
    A₂ u a b = (Complex.I * (conj (u a b 0) * deriv (fun t => u a t 0) b +
      conj (u a b 1) * deriv (fun t => u a t 1) b)).re := rfl



end Berry
