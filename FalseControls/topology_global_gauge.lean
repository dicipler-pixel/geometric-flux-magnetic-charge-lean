import FluxCharge
-- The north coefficient is a smooth scalar function with unequal endpoint values,
-- a_N(0) = 0 and a_N(π) = 1. The false endpoint equality must be rejected.
-- Regularity of a_N dφ as a sphere one-form is a separate geometric statement.
open MonopoleStance in
example : northCoefficient 0 = northCoefficient Real.pi := by
  simp [northCoefficient]

