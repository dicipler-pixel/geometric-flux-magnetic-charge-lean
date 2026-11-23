import FluxCharge
open MonopoleStance
example (r : ChargeRecord) (h : ElectromagneticBridge 0 r) :
    MagneticallyCharged r ↔ GeometricallyCharged r := by
  exact bridge_transfers_charge 0 (by norm_num) r h
