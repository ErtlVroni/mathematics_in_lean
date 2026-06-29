import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

#check le_antisymm
#check ge_antisymm


example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    · apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    · apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    · apply min_le_right
    · apply min_le_left
  apply le_antisymm
  · apply h
  · apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    · apply min_le_right
    · apply min_le_left

example : max a b = max b a := by
  apply ge_antisymm
  · show max b a ≤ max a b
    apply max_le
    · apply le_max_right
    · apply le_max_left
  · show max a b ≤ max b a
    apply max_le
    · apply le_max_right
    · apply le_max_left

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    · apply le_max_right
    · apply le_max_left
  apply ge_antisymm
  · apply h
  · apply h

example : max a b = max b a := by
  apply ge_antisymm
  repeat
    apply max_le
    · apply le_max_right
    · apply le_max_left




example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    have h₀ : min a b ≤ a := by apply min_le_left
    have h₁ : min a b ≤ b := by apply min_le_right
    have h₂ : min (min a b) c ≤ (min a b) := by
      apply min_le_left
    have h₃ : min (min a b) c ≤ a := by
      apply le_trans
      · apply h₂
      · apply h₀
    have h₄ : min (min a b) c ≤ b := by
      apply le_trans
      · apply h₂
      · apply h₁
    have h₅ : min (min a b) c ≤ c := by
      apply min_le_right
    have h₆ : min (min a b) c ≤ (min b c) := by
      apply le_min
      · apply h₄
      · apply h₅
    apply le_min
    · apply h₃
    · apply h₆
  · show min a (min b c) ≤ min (min a b) c
    have h₀' : min b c ≤ b := by apply min_le_left
    have h₁' : min b c ≤ c := by apply min_le_right
    have h₂' : min a (min b c) ≤ (min b c) := by
      apply min_le_right
    have h₃' : min a (min b c) ≤ b := by
      apply le_trans
      · apply h₂'
      · apply h₀'
    have h₄' : min a (min b c) ≤ c := by
      apply le_trans
      · apply h₂'
      · apply h₁'
    have h₅' : min a (min b c) ≤ a := by apply min_le_left
    have h₆' : min a (min b c) ≤ (min a b) := by
      apply  le_min
      · apply h₅'
      · apply h₃'
    apply le_min
    · apply h₆'
    · apply h₄'


example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · apply le_trans
      · apply min_le_left (min a b) c
      · apply min_le_left a b
    · apply le_min
      · apply le_trans
        · apply min_le_left (min a b) c
        · apply min_le_right a b
      · apply min_le_right (min a b) c
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · apply le_min
      · apply min_le_left
      · apply le_trans
        · apply min_le_right
        · apply min_le_left
    · apply le_trans
      · apply min_le_right
      · apply min_le_right

example : max (max a b) c = max a (max b c) := by
  apply le_antisymm
  · show max (max a b) c ≤ max a (max b c)
    have h₀ : b ≤ max b c := by apply le_max_left
    have h₁ : c ≤ max b c := by apply le_max_right
    have h₂ : a ≤ max a (max b c) := by apply le_max_left
    have h₃ : (max b c) ≤ max a (max b c) := by apply le_max_right
    have h₄ : b ≤ max a (max b c) := by
      apply le_trans
      · apply h₀
      · apply h₃
    have h₅ : c ≤ max a (max b c) := by
      apply le_trans
      · apply h₁
      · apply h₃
    have h₆ : (max a b) ≤ max a (max b c) := by
      apply max_le
      · apply h₂
      · apply h₄
    apply max_le
    · apply h₆
    · apply h₅
  · show  max a (max b c) ≤ max (max a b) c
    have h₀' : a ≤ (max a b) := by apply le_max_left
    have h₁' : b ≤ (max a b) := by apply le_max_right
    have h₂' : (max a b) ≤ max (max a b) c := by apply le_max_left
    have h₃' : a ≤ max (max a b) c := by
      apply le_trans
      · apply h₀'
      · apply h₂'
    have h₄' : b ≤ max (max a b) c := by
      apply le_trans
      · apply h₁'
      · apply h₂'
    have h₅' : c ≤ max (max a b) c := by
      apply le_max_right
    have h₆' : (max b c) ≤ max (max a b) c := by
      apply max_le
      · apply h₄'
      · apply h₅'
    apply max_le
    · apply h₃'
    · apply h₆'



theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h₀ : min a b ≤ a := by apply min_le_left
  have h₁ : min a b ≤ b := by apply min_le_right
  have h₂ : (min a b) + c ≤ a + c := by apply add_le_add_right h₀
  have h₃ : (min a b) + c ≤ b + c := by apply add_le_add_right h₁
  apply le_min
  · apply h₂
  · apply h₃

theorem aux1 : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right (min_le_left a b) c
  · apply add_le_add_right (min_le_right a b) c

theorem aux2 : min a b + c ≤ min (a + c) (b + c) :=
  le_min (add_le_add_right (min_le_left a b) c) (add_le_add_right (min_le_right a b) c)




example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · show min a b + c ≤ min (a + c) (b + c)
    exact aux a b c
  · show min (a + c) (b + c) ≤ min a b + c
    calc
      min (a + c) (b + c) = min (a + c) (b + c) + c + -c := by rw [add_neg_cancel_right]
      _ = min (a + c) (b + c) + -c + c :=  by ring
      _ ≤ min ((a + c) + -c) ((b + c) + -c) + c := by apply add_le_add_right (aux (a + c) (b + c) (-c)) c
      _ = min a b + c := by rw [add_neg_cancel_right, add_neg_cancel_right]

#check add_neg_cancel_right


#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

#check add_sub_cancel_right

example : |a| - |b| ≤ |a - b| := by
  calc
    |a| - |b|  = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by apply add_le_add_right (abs_add (a - b) b)
    _ = |a - b| := by rw [add_sub_cancel_right]

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h₀ : x ∣ (x * z) := by
    apply dvd_mul_right
  have h₁ : x ∣ y * (x * z) := by
    apply dvd_mul_of_dvd_right h₀
  have h₂ : x ∣ x^2 := by
    apply dvd_mul_left
  have h₃ : x ∣ w^2 := by
    apply dvd_mul_of_dvd_right h
  have h₄ : x ∣ y * (x * z) + x ^ 2  := by
    apply dvd_add h₁ h₂
  have h₅ : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
    apply dvd_add h₄ h₃
  exact h₅

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right (dvd_mul_right x z)
    · apply dvd_mul_left
  · apply dvd_mul_of_dvd_right h





end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  · show Nat.gcd m n ∣ Nat.gcd n m
    have h₀ : Nat.gcd m n ∣ n := by
      apply Nat.gcd_dvd_right m n
    have h₁ : Nat.gcd m n ∣ m := by
      apply Nat.gcd_dvd_left m n
    apply Nat.dvd_gcd h₀ h₁
  · show Nat.gcd n m ∣ Nat.gcd m n
    have h₀' : Nat.gcd n m ∣ m := by
      apply Nat.gcd_dvd_right n m
    have h₁' : Nat.gcd n m ∣ n := by
      apply Nat.gcd_dvd_left n m
    apply Nat.dvd_gcd h₀' h₁'



example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    · apply Nat.gcd_dvd_right
    · apply Nat.gcd_dvd_left

example : Nat.gcd m n = Nat.gcd n m := by
  have h : ∀ x y : ℕ , Nat.gcd y x ∣ Nat.gcd x y := by
    intro x y
    apply Nat.dvd_gcd
    · apply Nat.gcd_dvd_right
    · apply Nat.gcd_dvd_left
  apply Nat.dvd_antisymm
  · apply h
  · apply h


end
