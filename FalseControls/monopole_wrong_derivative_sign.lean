import FluxCharge.Monopole
-- The θ-derivative of the (0,0) entry of P(n(θ,φ)) = (1 - cos θ)/2 is +sin θ / 2.
-- Claiming -sin θ / 2 (a sign slip in the chain rule) must be rejected.
open MonopoleStance Complex Matrix in
example (θ φ : ℝ) :
    HasDerivAt (fun t => proj (nvec t φ) 0 0) (-((Real.sin θ : ℂ)) / 2) θ := by
  simpa [dproj, dθn] using hasDerivAt_proj_θ θ φ 0 0
