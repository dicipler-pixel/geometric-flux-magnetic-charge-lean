import FluxCharge.Monopole
import FluxCharge.Geometry

/-!
# The seam: one checked chain from the Pauli matrix to the integer

`FluxCharge.Monopole` derives the curvature `sin θ / 2` from the actual derivatives of the
lower Pauli projector `proj (n(θ, φ))`. `FluxCharge.Geometry` (the ported original package)
integrates `omega θ = sin θ / 2` to unit normalized flux, using its own encoding
`lowerProjector x y z` of the same matrix. This file joins them:

* `lowerProjector_eq_proj`  : the two encodings are the same matrix;
* `proj_nvec_idempotent`    : along the sphere, the derived projector is a genuine projector;
* `derivedCurvature_eq`     : the curvature computed from Lean's `deriv` of the projector
                               entries is `sin θ / 2` at every point (θ, φ);
* `derived_curvature_unit_flux` : integrated over the (θ, φ) coordinate rectangle, that
                               derived curvature has normalized flux exactly 1;
* `matrix_to_integer`       : the three statements together.

Not proved here: the line bundle, its Chern class as a topological invariant, the physical
pullback, and any electromagnetic identification. The bridge stays a hypothesis
(`ElectromagneticBridge` in `FluxCharge.Bridge`).
-/

namespace MonopoleStance

noncomputable section

open Matrix Complex

/-- The two encodings of the lower Pauli projector ½(I − n·σ) are the same matrix. -/
theorem lowerProjector_eq_proj (x y z : ℝ) : lowerProjector x y z = proj (x, y, z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerProjector, proj] <;> apply Complex.ext <;> simp <;> ring

/-- Along the sphere, the derived projector is idempotent: P(n(θ, φ))² = P(n(θ, φ)). -/
theorem proj_nvec_idempotent (θ φ : ℝ) :
    proj (nvec θ φ) * proj (nvec θ φ) = proj (nvec θ φ) := by
  have h : (Real.sin θ * Real.cos φ) ^ 2 + (Real.sin θ * Real.sin φ) ^ 2 + Real.cos θ ^ 2 = 1 := by
    have h1 := Real.sin_sq_add_cos_sq θ
    have h2 := Real.sin_sq_add_cos_sq φ
    linear_combination (Real.sin θ ^ 2) * h2 + h1
  have e := lowerProjector_eq_proj (Real.sin θ * Real.cos φ) (Real.sin θ * Real.sin φ) (Real.cos θ)
  rw [show nvec θ φ = (Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ) from rfl, ← e]
  exact lowerProjector_idempotent _ _ _ h

/-- The curvature i Tr(P [∂_θ P, ∂_φ P]) built from Lean's derivatives of the actual
projector entries, as a real function of (θ, φ). -/
def derivedCurvature (θ φ : ℝ) : ℝ :=
  let V : Matrix (Fin 2) (Fin 2) ℂ := fun i j => deriv (fun t => proj (nvec t φ) i j) θ
  let W : Matrix (Fin 2) (Fin 2) ℂ := fun i j => deriv (fun t => proj (nvec θ t) i j) φ
  (I * trace (proj (nvec θ φ) * (V * W - W * V))).re

/-- The derived curvature is `sin θ / 2` at every point. -/
theorem derivedCurvature_eq (θ φ : ℝ) : derivedCurvature θ φ = omega θ := by
  have h := berry_curvature_from_derivatives θ φ
  simp only at h
  simp only [derivedCurvature]
  rw [h]
  simp

/-- Flux of a curvature over the (θ, φ) coordinate rectangle, in the orientation dθ ∧ dφ. -/
def coordFlux (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ _φ in (0:ℝ)..(2 * Real.pi), ∫ θ in (0:ℝ)..Real.pi, F θ _φ

/-- For a curvature that depends only on θ, `coordFlux` is the original package's `sphereFlux`. -/
theorem coordFlux_eq_sphereFlux (f : ℝ → ℝ) : coordFlux (fun θ _ => f θ) = sphereFlux f := rfl

/-- **The seam closed.** The curvature computed from the actual derivatives of the Pauli
projector has normalized flux exactly 1. -/
theorem derived_curvature_unit_flux : coordFlux derivedCurvature / (2 * Real.pi) = 1 := by
  have e : derivedCurvature = fun θ _ => omega θ := by
    funext θ φ
    exact derivedCurvature_eq θ φ
  rw [e, coordFlux_eq_sphereFlux]
  exact omega_unit_normalizedFlux

/-- **From the matrix to the integer, in one statement.** Along the sphere the projector is a
projector, its derived curvature is `sin θ / 2`, and the derived curvature has normalized
flux 1. -/
theorem matrix_to_integer :
    (∀ θ φ : ℝ, proj (nvec θ φ) * proj (nvec θ φ) = proj (nvec θ φ)) ∧
    (∀ θ φ : ℝ, derivedCurvature θ φ = Real.sin θ / 2) ∧
    coordFlux derivedCurvature / (2 * Real.pi) = 1 :=
  ⟨proj_nvec_idempotent, derivedCurvature_eq, derived_curvature_unit_flux⟩

end

end MonopoleStance
