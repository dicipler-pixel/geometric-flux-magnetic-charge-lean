import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
Concrete algebra and flux normalization for the stance discussed with Jeromie Beasley.
The matrix is the lower Pauli projector.  The curvature coefficient is supplied
explicitly from IQGT Appendix B; this file does NOT derive the Berry-curvature
formula from that projector, construct a Chern class, or identify an EM field.
-/
namespace MonopoleStance
noncomputable section
open Matrix intervalIntegral

/-- Lower eigenprojector candidate (I - d·σ)/2, in fixed matrix coordinates. -/
def lowerProjector (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(1-z)/2, 0⟩, ⟨-x/2, y/2⟩;
     ⟨-x/2, -y/2⟩, ⟨(1+z)/2, 0⟩]

theorem lowerProjector_hermitian (x y z : ℝ) :
    (lowerProjector x y z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerProjector, Matrix.conjTranspose, Complex.star_def, Complex.ext_iff] <;> ring

theorem lowerProjector_idempotent (x y z : ℝ)
    (h : x^2 + y^2 + z^2 = 1) :
    lowerProjector x y z * lowerProjector x y z = lowerProjector x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerProjector, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    constructor <;> nlinarith [h]

theorem lowerProjector_trace (x y z : ℝ) :
    Matrix.trace (lowerProjector x y z) = 1 := by
  apply Complex.ext <;> simp [Matrix.trace, Fin.sum_univ_two, lowerProjector]
  ring

/-- The coefficient Ω_{θφ} of the displayed IQGT sphere curvature.
The coordinate area element is already included: no second sin θ factor. -/
def omega (theta : ℝ) : ℝ := Real.sin theta / 2

/-- Iterated coordinate integral in the orientation dθ ∧ dφ. -/
def sphereFlux (f : ℝ → ℝ) : ℝ :=
  ∫ _phi in (0:ℝ)..(2*Real.pi), ∫ theta in (0:ℝ)..Real.pi, f theta

/-- Normalized flux, not a definition or construction of a topological Chern class. -/
def normalizedFlux (f : ℝ → ℝ) : ℝ := sphereFlux f / (2*Real.pi)

theorem omega_polar_integral :
    (∫ theta in (0:ℝ)..Real.pi, omega theta) = 1 := by
  simp [omega, integral_div, integral_sin]

theorem omega_sphereFlux : sphereFlux omega = 2*Real.pi := by
  simp [sphereFlux, omega_polar_integral]

theorem omega_unit_normalizedFlux : normalizedFlux omega = 1 := by
  rw [normalizedFlux, omega_sphereFlux]
  exact div_self (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem omega_nonzero_normalizedFlux : normalizedFlux omega ≠ 0 := by
  rw [omega_unit_normalizedFlux]
  norm_num

/-- Opposite supplied curvature cancels the total flux; an individual sector
still has unit flux. No claim about a formal complement-bundle Chern class. -/
theorem opposite_flux_cancels :
    sphereFlux omega + sphereFlux (fun theta => -omega theta) = 0 := by
  simp only [sphereFlux, intervalIntegral.integral_neg]
  ring

/-- The polar gauge-coefficient primitives have the stated local curvature. -/
def northCoefficient (theta : ℝ) : ℝ := (1 - Real.cos theta) / 2
def southCoefficient (theta : ℝ) : ℝ := -(1 + Real.cos theta) / 2

theorem north_derivative (theta : ℝ) :
    HasDerivAt northCoefficient (omega theta) theta := by
  convert ((hasDerivAt_const theta (1:ℝ)).sub (Real.hasDerivAt_cos theta)).div_const 2 using 1
  simp [northCoefficient, omega]

theorem south_derivative (theta : ℝ) :
    HasDerivAt southCoefficient (omega theta) theta := by
  convert (((hasDerivAt_const theta (1:ℝ)).add (Real.hasDerivAt_cos theta)).neg).div_const 2 using 1
  simp [southCoefficient, omega]

theorem gauge_coefficient_difference (theta : ℝ) :
    northCoefficient theta - southCoefficient theta = 1 := by
  unfold northCoefficient southCoefficient
  ring

/-- Direct integral calculation for the supplied monopole radial field on a
unit sphere, B=g r̂/r². This does not construct a Maxwell solution or its source. -/
def radialFlux (g : ℝ) : ℝ := sphereFlux (fun theta => g * Real.sin theta)

theorem radialFlux_eq (g : ℝ) : radialFlux g = 4*Real.pi*g := by
  simp [radialFlux, sphereFlux, integral_const_mul, integral_sin]
  ring

theorem radialFlux_nonzero_iff (g : ℝ) : radialFlux g ≠ 0 ↔ g ≠ 0 := by
  rw [radialFlux_eq]
  simp [mul_ne_zero, Real.pi_ne_zero]

end
end MonopoleStance
