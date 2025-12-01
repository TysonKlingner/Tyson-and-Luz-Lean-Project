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
def lift_f (m n : ℕ) : ZMod m ⊗[ℤ] ZMod n →ₗ[ℤ] ZMod (Nat.gcd m n) :=
TensorProduct.lift (f m n)

-- I don't think this lemma is needed.
-- lemma rewriteZmod (m n : ℕ) (a b c : ZMod m ⊗[ℤ] ZMod n) :
  --(lift_f m n) a + (lift_f m n) b = (lift_f m n) c →
  --(lift_f m n) a = (lift_f m n) c - (lift_f m n) b := by
    --sorry

lemma rewritezero (m n : ℕ) : 0 = (lift_f m n) 0 := by
  exact (lift_f m n).map_zero

lemma kernel_of_lift_f (m n :  ℕ) (x : ZMod m ⊗[ℤ] ZMod n) :
  (lift_f m n) x = 0 → x = 0 := by
    intro h
    induction x using TensorProduct.induction_on with
    | zero =>
        exact rfl
    | tmul a₁ a₂ =>
      -- have h' : (f m n) a₁ a₂ = 0 := by
        -- simpa [lift_f] using h
      -- simp [f] at h'
      simp [lift_f] at h
      simp [f] at h
      sorry
    | add a₁ a₂ ha₁ ha₂ =>
      simp [lift_f] at h
      rw [add_eq_zero_iff_eq_neg] at h
      sorry
/-- Proof that lift_f is injective -/
lemma lift_f_injective (m n : ℕ) :
  Function.Injective (lift_f m n) := by
  intros a b h
  induction a using TensorProduct.induction_on with
  | zero =>
      simp [map_zero] at h
      exact Eq.symm (kernel_of_lift_f m n b (id (Eq.symm h)))
      -- handle a = 0
  | tmul a₁ a₂ =>
      -- handle pure tensor case a = (a₁ ⊗ a₂)
      rw [←(sub_eq_zero)] at h
      rw [sub_eq_add_neg] at h
      rw [←(lift_f m n).map_neg] at h
      rw [←(lift_f m n).map_add] at h
      apply kernel_of_lift_f at h
      exact sub_eq_zero.mp h
      -- apply rewritezero at h
  | add a₁ a₂ ha₁ ha₂ =>
      -- handle sum case a = a₁ + a₂
      rw [←sub_eq_zero] at h
      rw [sub_eq_add_neg] at h
      rw [←(lift_f m n).map_neg] at h
      rw [←(lift_f m n).map_add] at h
      apply kernel_of_lift_f at h
      exact sub_eq_zero.mp h
      --simp [map_add] at h
      --apply rewriteZmod at h
      --rw [sub_eq_add_neg] at h
      --rw [←(lift_f m n).map_neg] at h
      --rw [←(lift_f m n).map_add] at h
      -- apply (eq_sub_iff_add_eq) at h
      --



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

-- Outline of the final linear equivalence
/--
Canonical isomorphism:
ZMod m ⊗ ZMod n ≃ₗ[ℤ] ZMod (gcd m n)
-/
noncomputable def zmod_tensor_zmod (m n : ℕ) (h : m ≠ 0 ∨ n ≠ 0) :
  ZMod m ⊗[ℤ] ZMod n ≃ₗ[ℤ] ZMod (Nat.gcd m n) :=
    LinearEquiv.ofBijective (lift_f m n) (lift_f_bijective m n h)

theorem TensorRingIso (m n : ℕ) (h : m ≠ 0 ∨ n ≠ 0) :
  Nonempty (ZMod m ⊗[ℤ] ZMod n ≃ₗ[ℤ] ZMod (Nat.gcd m n)) := by
    apply Nonempty.intro
    exact zmod_tensor_zmod m n h
