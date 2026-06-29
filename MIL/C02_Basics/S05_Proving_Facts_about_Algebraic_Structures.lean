import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · show x ⊓ y ≤ y ⊓ x
    apply le_inf
    · apply inf_le_right
    · apply inf_le_left
  · show y ⊓ x ≤ x ⊓ y
    apply le_inf
    · apply inf_le_right
    · apply inf_le_left

example : x ⊓ y = y ⊓ x := by
  have h : ∀ a b : α, a ⊓ b ≤ b ⊓ a := by
    intro a b
    apply le_inf
    · apply inf_le_right
    · apply inf_le_left
  apply le_antisymm
  apply h
  apply h

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
  apply le_inf
  · apply inf_le_right
  · apply inf_le_left



example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z)
    have h₁ : x ⊓ y ≤ x := by apply inf_le_left
    have h₂ : x ⊓ y ≤ y := by apply inf_le_right
    have h₃ : (x ⊓ y) ⊓ z ≤ z := by apply inf_le_right
    have h₄ : (x ⊓ y) ⊓ z ≤ x  := by
      apply le_trans
      · apply inf_le_left
      · apply h₁
    have h₅ : (x ⊓ y) ⊓ z ≤ y := by
      apply le_trans
      · apply inf_le_left
      · apply h₂
    have h₆ : (x ⊓ y) ⊓ z ≤ (y ⊓ z) := by
      apply le_inf
      · apply h₅
      · apply h₃
    apply le_inf
    · apply h₄
    · apply h₆
  · show x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z
    have g₁ : (y ⊓ z) ≤ y := by apply inf_le_left
    have g₂ : (y ⊓ z) ≤ z := by apply inf_le_right
    have g₃ : x ⊓ (y ⊓ z) ≤ x := by apply inf_le_left
    have g₄ : x ⊓ (y ⊓ z) ≤ y := by
      apply le_trans
      · apply inf_le_right
      · apply g₁
    have g₅ : x ⊓ (y ⊓ z) ≤ z := by
      apply le_trans
      · apply inf_le_right
      · apply g₂
    have g₆ : x ⊓ (y ⊓ z) ≤ (x ⊓ y) := by
      apply le_inf
      · apply g₃
      · apply g₄
    apply le_inf
    · apply g₆
    · apply g₅

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z)
    apply le_inf
    · apply le_trans
      · apply inf_le_left
      · apply inf_le_left
    · apply le_inf
      · apply le_trans
        · apply inf_le_left
        · apply inf_le_right
      · apply inf_le_right
  · show x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z
    apply le_inf
    · apply le_inf
      · apply inf_le_left
      · apply le_trans
        · apply inf_le_right
        · apply inf_le_left
    · apply le_trans
      · apply inf_le_right
      · apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
  apply sup_le
  · apply le_sup_right
  · apply le_sup_left


example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry
#check inf_sup_self
theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    · apply le_refl x
    · apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · show x ⊔ (x ⊓ y) ≤ x
    apply sup_le
    · apply le_refl x
    · apply inf_le_left
  · show x ≤ x ⊔ (x ⊓ y)
    apply le_sup_left


end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)



example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h (a ⊔ b) a c]
  rw [inf_comm (a ⊔ b) a]
  rw [absorb1 a b]
  rw [inf_comm (a ⊔ b) c]
  rw [h c a b]
  rw [← sup_assoc]
  rw [inf_comm c a]
  rw [absorb2 a c]
  rw [inf_comm c b]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  · show a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c)
    have g₁ : a ⊓ (b ⊔ c) = a ⊓ ((a ⊓ b) ⊔ (a ⊓ c)) := by
      rw [sup_comm (a ⊓ b) (a ⊓ c)]
      rw [h (a ⊓ c) a b]
      rw [sup_comm (a ⊓ c) a]
      rw [sup_comm (a ⊓ c) b]
      rw [← inf_assoc]
      rw [absorb1 a (a ⊓ c)]
      rw [h b a c]
      rw [sup_comm b a]
      rw [← inf_assoc]
      rw [absorb1 a b]
    calc
      a ⊓ (b ⊔ c) = a ⊓ ((a ⊓ b) ⊔ (a ⊓ c)) := by apply g₁
      _ ≤ (a ⊓ b) ⊔ (a ⊓ c) := by apply inf_le_right

  · show (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)
    have h₁ : a ⊓ b ≤ a := by apply inf_le_left
    have h₂ : a ⊓ c ≤ a := by apply inf_le_left
    have h₃ : (a ⊓ b) ⊔ (a ⊓ c) ≤ a := by
      apply sup_le
      · apply h₁
      · apply h₂
    have h₄ : b ≤ b ⊔ c := by apply le_sup_left
    have h₅ : c ≤ b ⊔ c := by apply le_sup_right
    have h₆ : a ⊓ b ≤ b := by apply inf_le_right
    have h₇ : a ⊓ c ≤ c := by apply inf_le_right
    have h₈ : a ⊓ b ≤ b ⊔ c := by
      apply le_trans
      · apply h₆
      · apply h₄
    have h₉ : a ⊓ c ≤ b ⊔ c := by
      apply le_trans
      · apply h₇
      · apply h₅
    have h10 : (a ⊓ b) ⊔ (a ⊓ c) ≤ b ⊔ c := by
      apply sup_le
      · apply h₈
      · apply h₉
    apply le_inf
    · apply h₃
    · apply h10

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h (a ⊓ b) a c]
  rw [sup_comm (a ⊓ b) a]
  rw [absorb2 a b]
  rw [sup_comm (a ⊓ b) c]
  rw [h c a b]
  rw [← inf_assoc a (c ⊔ a) (c ⊔ b)]
  rw [sup_comm c a]
  rw [absorb1 a c]
  rw [sup_comm c b]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check add_le_add_right
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem ineq1  (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a]
  rw [sub_eq_add_neg a a]
  rw [sub_eq_add_neg b a]
  apply add_le_add_right
  exact h


theorem ineq2 (h: 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a]
  rw [← add_zero b]
  rw [← sub_self a]
  rw [sub_eq_add_neg a a]
  rw [add_comm a (-a)]
  rw [← add_assoc]
  rw [← add_assoc]
  rw [← sub_eq_add_neg a a]
  rw [← sub_eq_add_neg b a]
  rw [sub_self]
  apply add_le_add_right
  exact h





example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₀ : 0 ≤ b - a := by apply ineq1 a b h
  have h₁ : 0 ≤ (b - a) * c := by apply mul_nonneg h₀ h'
  rw [sub_mul b a c] at h₁
  apply ineq2 (a*c) (b*c) h₁






end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
#check nonneg_of_mul_nonneg_left

example (x y : X) : 0 ≤ dist x y := by
  have h₀ :  dist x y + dist y x = dist x y * 2 := by
    rw [dist_comm y x]
    rw [← two_mul]
    rw [mul_comm]
  have h₁ : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  have h₂ : 0 ≤ dist x y * 2
  calc
    0 ≤ dist x y + dist y x := by apply h₁
    _ = dist x y * 2 := by apply h₀
  have h₃ : (0 : ℝ) < 2 := by norm_num
  apply nonneg_of_mul_nonneg_left h₂ h₃



















end
