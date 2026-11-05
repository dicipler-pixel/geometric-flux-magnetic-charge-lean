import FluxCharge.Seam

/-!
# Pole obstruction, latitude-cut independence and derived band-flux cancellation

* `no_global_regular_gauge` rules out a real primitive of ω with equal endpoint values at
  0 and π. This is the scalar pole obstruction for the axisymmetric coefficient ansatz;
  arbitrary sphere one-forms and their regularity are not encoded.
* `flux_is_transition_jump` and `flux_one_at_every_cut` identify the split polar integral
  with the fixed north/south coefficient difference, equal to 1 at every real cut. This is
  latitude-cut independence, not general coordinate or gauge invariance.
* Actual entrywise derivatives of `1 − P` give the opposite curvature and normalized flux
  −1. `total_chern_zero` states cancellation of normalized real fluxes; its historical name
  does not denote a constructed Chern class.

The eigenline bundle, Chern class, general coordinate/gauge invariance, spatial pullback
and electromagnetic identification remain outside this formalization.
-/

namespace MonopoleStance

noncomputable section

open Matrix Complex intervalIntegral

theorem continuous_omega : Continuous omega := by
  unfold omega
  exact Real.continuous_sin.div_const 2

/-- **Pole obstruction.** No real primitive of `ω` takes equal values at 0 and π.
This scalar statement does not quantify over arbitrary sphere one-forms. -/
theorem no_global_regular_gauge :
    ¬ ∃ a : ℝ → ℝ, (∀ θ, HasDerivAt a (omega θ) θ) ∧ a 0 = a Real.pi := by
  rintro ⟨a, ha, hpole⟩
  have h := integral_eq_sub_of_hasDerivAt (fun x _ => ha x)
    (continuous_omega.intervalIntegrable 0 Real.pi)
  rw [omega_polar_integral] at h
  linarith

/-- **Latitude-cut independence for the fixed coefficients.** The split polar integral equals
`a_N(θ₀) − a_S(θ₀)`. Cap language applies for cuts in [0, π]; the identity holds for all real cuts. -/
theorem flux_is_transition_jump (θ₀ : ℝ) :
    (∫ θ in (0:ℝ)..θ₀, omega θ) + (∫ θ in θ₀..Real.pi, omega θ) =
      northCoefficient θ₀ - southCoefficient θ₀ := by
  have hN := integral_eq_sub_of_hasDerivAt (fun x _ => north_derivative x)
    (continuous_omega.intervalIntegrable 0 θ₀)
  have hS := integral_eq_sub_of_hasDerivAt (fun x _ => south_derivative x)
    (continuous_omega.intervalIntegrable θ₀ Real.pi)
  rw [hN, hS]
  have h0 : northCoefficient 0 = 0 := by simp [northCoefficient]
  have hπ : southCoefficient Real.pi = 0 := by simp [southCoefficient]
  rw [h0, hπ]
  ring

/-- For every cut, the jump, and so the polar flux, is exactly 1. -/
theorem flux_one_at_every_cut (θ₀ : ℝ) :
    (∫ θ in (0:ℝ)..θ₀, omega θ) + (∫ θ in θ₀..Real.pi, omega θ) = 1 := by
  rw [flux_is_transition_jump, gauge_coefficient_difference]

/-- Derivative of each entry of the complementary projector `1 − P` along θ is `−D(∂_θ n)`. -/
theorem hasDerivAt_compl_θ (θ φ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => ((1 : Matrix (Fin 2) (Fin 2) ℂ) - proj (nvec t φ)) i j)
      (-(dproj (dθn θ φ) i j)) θ := by
  simp only [Matrix.sub_apply]
  exact ((hasDerivAt_const θ ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)).sub
    (hasDerivAt_proj_θ θ φ i j)).congr_deriv (by simp)

/-- Derivative of each entry of `1 − P` along φ is `−D(∂_φ n)`. -/
theorem hasDerivAt_compl_φ (θ φ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => ((1 : Matrix (Fin 2) (Fin 2) ℂ) - proj (nvec θ t)) i j)
      (-(dproj (dφn θ φ) i j)) φ := by
  simp only [Matrix.sub_apply]
  exact ((hasDerivAt_const φ ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)).sub
    (hasDerivAt_proj_φ θ φ i j)).congr_deriv (by simp)

/-- The complementary band's curvature, built from Lean's derivatives of the entries of `1 − P`. -/
def derivedCurvatureCompl (θ φ : ℝ) : ℝ :=
  let V : Matrix (Fin 2) (Fin 2) ℂ :=
    fun i j => deriv (fun t => ((1 : Matrix (Fin 2) (Fin 2) ℂ) - proj (nvec t φ)) i j) θ
  let W : Matrix (Fin 2) (Fin 2) ℂ :=
    fun i j => deriv (fun t => ((1 : Matrix (Fin 2) (Fin 2) ℂ) - proj (nvec θ t)) i j) φ
  (I * trace ((1 - proj (nvec θ φ)) * (V * W - W * V))).re

/-- The complementary band carries curvature `−sin θ / 2` at every point. -/
theorem derivedCurvatureCompl_eq (θ φ : ℝ) : derivedCurvatureCompl θ φ = -omega θ := by
  have hV : (fun i j => deriv (fun t => ((1 : Matrix (Fin 2) (Fin 2) ℂ) - proj (nvec t φ)) i j) θ
      : Matrix (Fin 2) (Fin 2) ℂ) = -dproj (dθn θ φ) := by
    ext i j
    rw [Matrix.neg_apply]
    exact (hasDerivAt_compl_θ θ φ i j).deriv
  have hW : (fun i j => deriv (fun t => ((1 : Matrix (Fin 2) (Fin 2) ℂ) - proj (nvec θ t)) i j) φ
      : Matrix (Fin 2) (Fin 2) ℂ) = -dproj (dφn θ φ) := by
    ext i j
    rw [Matrix.neg_apply]
    exact (hasDerivAt_compl_φ θ φ i j).deriv
  simp only [derivedCurvatureCompl]
  rw [hV, hW, neg_mul_neg, neg_mul_neg, complement_curvature, triple_product]
  simp [omega, Complex.sin_ofReal_re]

/-- The complementary band has normalized flux −1. -/
theorem derived_compl_flux : coordFlux derivedCurvatureCompl / (2 * Real.pi) = -1 := by
  have e : derivedCurvatureCompl = fun θ _ => -omega θ := by
    funext θ φ
    exact derivedCurvatureCompl_eq θ φ
  have h := opposite_flux_cancels
  have h1 := omega_unit_normalizedFlux
  rw [e, coordFlux_eq_sphereFlux (fun θ => -omega θ)]
  unfold normalizedFlux at h1
  have hpi : (2 * Real.pi) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hs : sphereFlux (fun θ => -omega θ) = -sphereFlux omega := by linarith
  rw [hs, neg_div, h1]

/-- **Derived band-flux cancellation.** The normalized real fluxes sum to zero.
The historical theorem name does not assert a formal Chern-class construction. -/
theorem total_chern_zero :
    coordFlux derivedCurvature / (2 * Real.pi) + coordFlux derivedCurvatureCompl / (2 * Real.pi) = 0 := by
  rw [derived_curvature_unit_flux, derived_compl_flux]
  norm_num

end

end MonopoleStance

