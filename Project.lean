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


/-- Proof that lift_f is injective -/
lemma lift_f_injective (m n : ℕ) :
  Function.Injective (lift_f m n) := by
  intros a b h
  induction a using TensorProduct.induction_on with
  | zero =>
      -- handle a = 0
      sorry
  | tmul a₁ a₂ =>
      -- handle pure tensor case a = (a₁ ⊗ a₂)
      sorry
  | add a₁ a₂ ha₁ ha₂ =>
      -- handle sum case a = a₁ + a₂
      sorry


/-- Proof that lift_f is surjective -/
lemma lift_f_surjective (m n : ℕ) (h : m ≠ 0 ∨ n ≠ 0) : -- Modify assumptions.
  Function.Surjective (lift_f m n) := by
  intro z
  -- Any z : ZMod (gcd m n) is the image of some element in ZMod m ⨂ ZMod n.
  let k := z.val
  -- Use generator 1 ⊗ k to hit z
  use (1 : ZMod m) ⊗ₜ (k : ZMod n)
  simp [lift_f, f, k, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
  -- New goal: ↑z.val = z
  -- Proving m.gcd n ≠ 0.
  have gcd_not_zero :
  m.gcd n ≠ 0 := by
    by_cases hm : (m ≠ 0)
      -- Positive case (m ≠ 0)
    · exact Nat.gcd_ne_zero_left hm
      -- Negative case (m = 0)
    · have hn: n ≠ 0 := Or.resolve_left h hm
      exact Nat.gcd_ne_zero_right hn

  have : NeZero (m.gcd n) := ⟨gcd_not_zero⟩
  -- Apply this result that requires m.gcd n ≠ 0 to close the goal.
  exact ZMod.natCast_zmod_val z


lemma lift_f_bijective (m n : ℕ) (h : m ≠ 0 ∨ n ≠ 0) :
  Function.Bijective (lift_f m n) := by
  use lift_f_injective m n
  use lift_f_surjective m n h

-- It seems like we don't need this anymore.
def inv_f (m n : ℕ) : ZMod (Nat.gcd m n) → ZMod m ⊗[ℤ] ZMod n :=
  (fun x =>
      ((1 : ZMod m) ⊗ₜ (x.val : ZMod n)))


-- Outline of the final linear equivalence
/--
Canonical isomorphism:
ZMod m ⊗ ZMod n ≃ₗ[ℤ] ZMod (gcd m n)
-/
noncomputable def zmod_tensor_zmod (m n : ℕ) (h : m ≠ 0 ∨ n ≠ 0): ZMod m ⊗[ℤ] ZMod n ≃ₗ[ℤ] ZMod (Nat.gcd m n) :=
LinearEquiv.ofBijective (lift_f m n) (lift_f_bijective m n h)

theorem TensorRingIso (m n : ℕ) (h : m ≠ 0 ∨ n ≠ 0): Nonempty (ZMod m ⊗[ℤ] ZMod n ≃ₗ[ℤ] ZMod (Nat.gcd m n)) := by
  apply Nonempty.intro
  exact zmod_tensor_zmod m n h
