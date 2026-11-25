import FluxCharge
-- The gauge law is A ↦ A − dλ, not A ↦ A + dλ. Take the constant spinor u = (1, 0) and λ(a, b) = a.
-- Then A₁ of e^{iλ}u is −1 at the origin, while A₁ of u is 0 and dλ = 1, so the plus-sign law
-- asserts −1 = 1. It must be rejected for that arithmetic reason, not for a missing name.
open Berry in
example :
    A₁ (gauge (fun a _ => a) (fun _ _ => (![1, 0] : Fin 2 → ℂ))) 0 0
      = A₁ (fun _ _ => (![1, 0] : Fin 2 → ℂ)) 0 0 + deriv (fun s : ℝ => s) 0 := by
  have hconst : A₁ (fun _ _ => (![1, 0] : Fin 2 → ℂ)) 0 0 = 0 := by
    simp [A₁, A, connRe, B, deriv_const]
  rw [A_gauge_sub (u := fun _ _ => (![1, 0] : Fin 2 → ℂ)) (lambda := fun a _ => a)
    (a := 0) (b := 0), hconst]
  · simp [A₁, A, connRe, B, deriv_const]
  · intro k; exact differentiableAt_const _
  · exact differentiableAt_id
  · simp
