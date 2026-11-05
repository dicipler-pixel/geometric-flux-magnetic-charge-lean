import FluxCharge
-- The derived curvature has normalized flux 1, not 2 (a doubled area element is the usual slip).
open MonopoleStance in
example : coordFlux derivedCurvature / (2 * Real.pi) = 2 := by
  rw [derived_curvature_unit_flux]
  norm_num
