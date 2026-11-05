import FluxCharge
-- The two bands carry +1 and -1; claiming they add to 2 (forgetting the sign of the
-- complementary curvature) must fail.
open MonopoleStance in
example :
    coordFlux derivedCurvature / (2 * Real.pi) + coordFlux derivedCurvatureCompl / (2 * Real.pi) = 2 := by
  rw [derived_curvature_unit_flux, derived_compl_flux]
  norm_num
