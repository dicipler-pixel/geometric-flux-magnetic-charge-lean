import FluxCharge.Monopole
-- The Berry curvature of the lower Pauli eigenline is sin θ / 2, not sin θ: the factor 1/2 is the
-- projector's own (P = (I - n·σ)/2), and dropping it is the commonest error in this calculation.
open MonopoleStance Complex Matrix in
example (θ φ : ℝ) :
    I * trace (proj (nvec θ φ) *
      (dproj (dθn θ φ) * dproj (dφn θ φ) - dproj (dφn θ φ) * dproj (dθn θ φ))) =
      ((Real.sin θ : ℝ) : ℂ) := by
  rw [curvature_formula, triple_product]
  simp
