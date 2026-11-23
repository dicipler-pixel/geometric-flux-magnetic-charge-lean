import FluxCharge
open MonopoleStance
example : lowerProjector 0 0 0 * lowerProjector 0 0 0 = lowerProjector 0 0 0 := by
  apply lowerProjector_idempotent
  norm_num
