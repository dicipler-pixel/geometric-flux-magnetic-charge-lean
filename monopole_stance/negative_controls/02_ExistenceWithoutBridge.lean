import MonopoleStance
open MonopoleStance
example : ∀ r : ChargeRecord, GeometricallyCharged r → MagneticallyCharged r := by
  intro r h
  exact h
