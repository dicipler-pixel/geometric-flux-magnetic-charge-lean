import MonopoleStance
open MonopoleStance
example (theta : ℝ) : northCoefficient theta - southCoefficient theta = 0 := by
  rw [gauge_coefficient_difference]
  norm_num
