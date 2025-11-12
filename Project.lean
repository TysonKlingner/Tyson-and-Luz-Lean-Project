import Mathlib

open scoped TensorProduct

variable (m n : ℕ)

def d := (Nat.gcd n m)

theorem TensorRingIso (m n : ℕ) : Nonempty ((TensorProduct ℤ (ZMod n)  (ZMod m))
  ≃ₗ[ℤ] ZMod (Nat.gcd n m)):= by sorry
