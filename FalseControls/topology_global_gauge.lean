import FluxCharge
-- The north coefficient a_N has a_N' = ω, but a_N(0) = 0 and a_N(π) = 1: it is not regular at
-- both poles. Claiming it is (a single global gauge) must fail.
open MonopoleStance in
example : northCoefficient 0 = northCoefficient Real.pi := by
  simp [northCoefficient]
