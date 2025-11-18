import Mathlib
open TensorProduct

/-!
# Tensor product of ZMod

We construct the canonical isomorphism
ZMod m ⊗ ZMod n ≃ ZMod (Nat.gcd m n)
-/
-- Bilinear map: ZMod m × ZMod n → ZMod (gcd m n)
def f (m n : ℕ) :
    ZMod m →ₗ[ℤ] ZMod n →ₗ[ℤ] ZMod (Nat.gcd m n) :=
  LinearMap.mk₂ ℤ
    (fun x y =>
      (ZMod.castHom (Nat.gcd_dvd_left m n) _ x) *
      (ZMod.castHom (Nat.gcd_dvd_right m n) _ y))
    -- H1 : additivity in the first argument
    (by
      intros x₁ x₂ y
      simp [map_add, add_mul])
    -- H2 : ℤ-linearity in the first argument
    (by
      intros a x y
      simp [mul_comm, map_mul, mul_assoc])
    -- H3 : additivity in the second argument
    (by
      intros x y₁ y₂
      simp [map_add, mul_add])
    -- H4 : ℤ-linearity in the second argument
    (by
      intros a x y
      simp [mul_comm, map_mul, mul_left_comm])


-- Lift to a map on the tensor product
def lift_f (m n : ℕ)  : ZMod m ⊗[ℤ] ZMod n →ₗ[ℤ] ZMod (Nat.gcd m n) :=
TensorProduct.lift (f m n)


/-- Proof that lift_f is surjective -/
lemma lift_f_surjective (m n : ℕ) {hm : m ≠ 0} {hn : n ≠ 0} : -- Modify assumptions.
  Function.Surjective (lift_f m n) := by
  intro z
  -- Any z : ZMod (gcd m n) is the image of some element in ZMod m ⨂ ZMod n.
  let k := z.val
  -- Use generator 1 ⊗ k to hit z
  use (1 : ZMod m) ⊗ₜ (k : ZMod n)
  simp [lift_f, f, k, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
  -- New goal: ↑z.val = z
  have gcd_ne_zero : m.gcd n ≠ 0 := Nat.gcd_ne_zero_left hm
  have gcd_ne_zero_inst : NeZero (m.gcd n) := ⟨gcd_ne_zero⟩ -- Why?!
  exact ZMod.natCast_zmod_val z

/-- Proof that lift_f is injective -/
lemma lift_f_injective (m n : ℕ) :
  Function.Injective (lift_f m n) := by
  intros a b h
  -- Let x₁ x₂ in ZMod m and y₁ y₂ in ZMod n.
  -- Assume f(x₁ ⨂ y₁) = f(x₂ ⨂ y₂) = k.
  -- Then (x₁ ⨂ x₂) = (1 ⨂ x₁x₂) = (1 ⨂ f(x₁ ⨂ x₂))
  -- Similary for the other term. Conclude from assumption.
  sorry


-- Outline of the final linear equivalence
/--
Canonical isomorphism:
ZMod m ⊗ ZMod n ≃ₗ[ℤ] ZMod (gcd m n)
-/
def zmod_tensor_zmod (m n : ℕ) : ZMod m ⊗[ℤ] ZMod n ≃ₗ[ℤ] ZMod (Nat.gcd m n) :=
LinearEquiv.ofBijective (lift_f m n)
  (by lift_f_injective m n)
  (by lift_f_surjective m n)

theorem TensorRingIso (m n : ℕ) : Nonempty (((ZMod n)⊗[ℤ](ZMod m)) ≃ₗ[ℤ] ZMod (Nat.gcd n m)):= by
  use zmod_tensor_zmod n m
