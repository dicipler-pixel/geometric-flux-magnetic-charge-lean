import FluxCharge.Seam

/-!
# Why the integer is topological

Three statements that go one step below "the flux is 1":

* `no_global_regular_gauge` : no single potential `a` with `a' = ω` takes the same value at the
  two poles. A regular global gauge would force the flux to be 0. The unit flux therefore forces
  two charts (Dirac's argument in miniature).
* `flux_is_transition_jump` : for every cut θ₀, the total flux equals the jump
  `a_N(θ₀) − a_S(θ₀)` between the north and south gauge coefficients, and that jump is 1
  (`flux_one_at_every_cut`). The integer lives in the transition between the charts, not in a
  coordinate choice.
* `derivedCurvatureCompl_eq`, `total_chern_zero` : the complementary band's curvature, built from
  the actual derivatives of `1 − P`, is `−sin θ / 2`. Its normalized flux is `−1`, so the two
  bands' fluxes sum to 0.

Not proved here: the line bundle and its Chern class as a topological invariant, the physical
pullback, or any electromagnetic identification.
-/

namespace MonopoleStance

noncomputable section

open Matrix Complex intervalIntegral

theorem continuous_omega : Continuous omega := by
  unfold omega
  exact Real.continuous_sin.div_const 2

/-- **No single regular gauge.** No potential with derivative `ω` takes equal values at the two
poles (in particular, none vanishes at both). -/
theorem no_global_regular_gauge :
    ¬ ∃ a : ℝ → ℝ, (∀ θ, HasDerivAt a (omega θ) θ) ∧ a 0 = a Real.pi := by
  rintro ⟨a, ha, hpole⟩
  have h := integral_eq_sub_of_hasDerivAt (fun x _ => ha x)
    (continuous_omega.intervalIntegrable 0 Real.pi)
  rw [omega_polar_integral] at h
  linarith

/-- **The flux is the gauge jump at any cut.** Integrating ω on the north cap with `a_N` and on
the south cap with `a_S` gives `a_N(θ₀) − a_S(θ₀)`, whatever the cut θ₀. -/
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
  simp [omega]

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

/-- **Total Chern number zero.** The two bands' derived fluxes cancel exactly. -/
theorem total_chern_zero :
    coordFlux derivedCurvature / (2 * Real.pi) + coordFlux derivedCurvatureCompl / (2 * Real.pi) = 0 := by
  rw [derived_curvature_unit_flux, derived_compl_flux]
  norm_num

end

end MonopoleStance
