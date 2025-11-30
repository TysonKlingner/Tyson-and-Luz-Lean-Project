import Mathlib
import Mathlib.LinearAlgebra.BilinearMap
open TensorProduct
open Fintype


--Practice Functions

--def f : ℕ → ℕ :=
  --fun n => 3*n+2

--#eval f 4

--def h : ℤ → ZMod 2 ⊗[ℤ] ZMod 4 :=
  --fun x => (x : ZMod 2)⊗ₜ(1: ZMod 4)

-- #eval h 9

--Defining the explicit (left) inverse

def g (m n : ℕ) :
    ZMod (Nat.gcd m n) -> (ZMod m ⊗[ℤ] ZMod n) :=
    (fun x => (x.val * ((m / m.gcd n) : ZMod m))⊗ₜ(1 : ZMod n))

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

example : 2 + 2 = 4 := by rfl

example : 17*((1 : ZMod 2)⊗ₜ[ℤ](1 : ZMod 2)) = 3*((1 : ZMod 2)⊗ₜ[ℤ](1 : ZMod 2)) := by rfl

#eval 4%2

def a : ZMod 2 ⊗[ℤ] ZMod 2 := 3*((1 : ZMod 2)⊗ₜ[ℤ](1 : ZMod 2))
def b : ZMod 2 ⊗[ℤ] ZMod 2 := 15*((1 : ZMod 2)⊗ₜ[ℤ](1 : ZMod 2))

lemma sanity : a - b = 0 := by
  exact sub_self a

lemma divisibility (n : ℕ) [NeZero n] (a b : ZMod n) : (a.val + b.val) % n = (a+b).val := by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.val_add

def ginv (m n : ℕ) : ZMod (Nat.gcd m n) →ₗ[ℤ] ZMod m ⊗[ℤ] ZMod n :=
{ toFun := (fun x => (x.val * ((m / m.gcd n) : ZMod m))⊗ₜ(1 : ZMod n))
  map_add' := by sorry
    -- intro a b
  map_smul' := by sorry
    --intro r x
    --exact?
}

def double : ℝ →ₗ[ℝ] ℝ :=
{ toFun      := fun x => 2 * x,
  map_add'   := by intro a b; ring,
  map_smul'  := by intro r x; exact mul_smul_comm r 2 x }
