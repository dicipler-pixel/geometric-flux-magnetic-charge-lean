import FluxCharge.Geometry

/-! Ported unchanged in content from the original Lean v4.19.0 archive (`monopole_stance/`).

The epistemic boundary is formalized as independence in a deliberately small
record language. Countermodels here are assignments of two numerical records,
NOT physical universes or Maxwell solutions.  Physical existence remains an
empirical question outside this formalization.
-/
namespace MonopoleStance

structure ChargeRecord where
  geometricCharge : ℤ
  magneticFlux : ℝ

def GeometricallyCharged (r : ChargeRecord) : Prop := r.geometricCharge ≠ 0
def MagneticallyCharged (r : ChargeRecord) : Prop := r.magneticFlux ≠ 0

/-- Extra physical identification, including a dimensional flux unit q.
Neither q nor this equality is derived from projector algebra. -/
def ElectromagneticBridge (q : ℝ) (r : ChargeRecord) : Prop :=
  r.magneticFlux = q * (r.geometricCharge : ℝ)

theorem bridge_transfers_charge (q : ℝ) (hq : q ≠ 0) (r : ChargeRecord)
    (hbridge : ElectromagneticBridge q r) :
    MagneticallyCharged r ↔ GeometricallyCharged r := by
  unfold MagneticallyCharged GeometricallyCharged
  rw [hbridge]
  simp [mul_ne_zero, hq]

def zeroMagneticRecord (n : ℤ) : ChargeRecord := ⟨n, 0⟩
def unitMagneticRecord (n : ℤ) : ChargeRecord := ⟨n, 1⟩

theorem same_geometry_opposite_magnetic_status (n : ℤ) :
    (zeroMagneticRecord n).geometricCharge = (unitMagneticRecord n).geometricCharge ∧
    ¬MagneticallyCharged (zeroMagneticRecord n) ∧
    MagneticallyCharged (unitMagneticRecord n) := by
  simp [zeroMagneticRecord, unitMagneticRecord, MagneticallyCharged]

theorem unit_geometry_compatible_with_both_records :
    (∃ r : ChargeRecord, r.geometricCharge = 1 ∧ ¬MagneticallyCharged r) ∧
    (∃ r : ChargeRecord, r.geometricCharge = 1 ∧ MagneticallyCharged r) := by
  constructor
  · exact ⟨zeroMagneticRecord 1, rfl, by simp [MagneticallyCharged, zeroMagneticRecord]⟩
  · exact ⟨unitMagneticRecord 1, rfl, by simp [MagneticallyCharged, unitMagneticRecord]⟩

theorem no_unconditional_existence_inference :
    ¬ (∀ r : ChargeRecord, GeometricallyCharged r → MagneticallyCharged r) := by
  intro h
  have bad := h (zeroMagneticRecord 1) (by
    simp [GeometricallyCharged, zeroMagneticRecord])
  simp [MagneticallyCharged, zeroMagneticRecord] at bad

theorem no_unconditional_absence_inference :
    ¬ (∀ r : ChargeRecord, GeometricallyCharged r → ¬MagneticallyCharged r) := by
  intro h
  exact h (unitMagneticRecord 1) (by
    simp [GeometricallyCharged, unitMagneticRecord]) (by
    simp [MagneticallyCharged, unitMagneticRecord])

/-- The zero-flux assignment cannot satisfy a nonzero-unit bridge at unit charge. -/
theorem unit_geometry_zero_flux_excludes_bridge (q : ℝ) (hq : q ≠ 0) :
    ¬ ElectromagneticBridge q (zeroMagneticRecord 1) := by
  simpa [ElectromagneticBridge, zeroMagneticRecord] using Ne.symm hq

/-- A bridge-compatible numerical record exists for every geometric integer.
Compatibility of records is weaker than physical realization. -/
theorem bridge_record_exists (q : ℝ) (n : ℤ) :
    ∃ r : ChargeRecord, r.geometricCharge = n ∧ ElectromagneticBridge q r := by
  exact ⟨⟨n, q*(n:ℝ)⟩, rfl, rfl⟩

/-- No-flux admissibility is a restriction of a model class, not a universal
absence theorem: a countermodel outside the class still exists in this language. -/
def AdmissibleNoFlux (r : ChargeRecord) : Prop := r.magneticFlux = 0

theorem admissibility_is_restriction :
    (∀ r : ChargeRecord, AdmissibleNoFlux r → ¬MagneticallyCharged r) ∧
    ¬ (∀ r : ChargeRecord, ¬MagneticallyCharged r) := by
  constructor
  · intro r h hne
    exact hne h
  · intro h
    exact h (unitMagneticRecord 1) (by simp [MagneticallyCharged, unitMagneticRecord])

/-- The exact stance: the supplied curvature has unit normalized flux; within
this record language that fact permits both magnetic assignments; a nonzero-unit
bridge is sufficient to transfer nonzero charge. -/
theorem formal_stance :
    normalizedFlux omega = 1 ∧
    ((∃ r : ChargeRecord, r.geometricCharge = 1 ∧ ¬MagneticallyCharged r) ∧
     (∃ r : ChargeRecord, r.geometricCharge = 1 ∧ MagneticallyCharged r)) ∧
    (∀ (q : ℝ), q ≠ 0 → ∀ r : ChargeRecord,
      ElectromagneticBridge q r → (MagneticallyCharged r ↔ GeometricallyCharged r)) := by
  exact ⟨omega_unit_normalizedFlux, unit_geometry_compatible_with_both_records,
    bridge_transfers_charge⟩

end MonopoleStance
