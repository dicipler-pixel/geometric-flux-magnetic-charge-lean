import MonopoleStance
open MonopoleStance
example : normalizedFlux omega = 0 := by
  rw [omega_unit_normalizedFlux]
  norm_num
