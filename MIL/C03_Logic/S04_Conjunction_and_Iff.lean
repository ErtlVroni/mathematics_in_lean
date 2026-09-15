import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  constructor
  · apply h₀
  · apply h



example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  apply h₁
  show x = y
  exact (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  push_neg
  apply lt_iff_le_and_ne.mpr h

 #check lt_iff_le_and_ne

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro (h' : y ≤ x)
  apply h.right
  show x = y
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')



example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  constructor
  · apply h.left
  by_contra h'
  apply h.right
  exact dvd_antisymm h.left h'

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  ⟨h.left, fun h' ↦ h.right (Nat.dvd_antisymm h.left h')⟩

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  have h₀ : ¬n ∣ m := by
    by_contra h'
    exact h.right (dvd_antisymm h.left h')
  ⟨h.left, h₀⟩

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  cases h
  next h₁ h₂ =>
    constructor
    · apply h₁
    intro h'
    · apply h₂
      exact dvd_antisymm h₁ h'

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply Nat.dvd_antisymm h0 h2



example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use (3 : ℝ)
  have h₁ : (2 : ℝ) < (3 : ℝ) := by norm_num
  have h₂ : (3 : ℝ) < (4 : ℝ) := by norm_num
  constructor
  · apply h₁
  · apply h₂

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num



example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example {x y : ℝ}  (h : ∃ z : ℝ, x < z ∧ z < y) : x < y := by
  rcases h with ⟨z, xltz : x < z, zlty : z < y⟩
  show x < y
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, (xltz : x < z), (zlty : z < y)⟩ ↦ lt_trans xltz zlty



example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num



example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')



example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose
    push_neg
    rintro h'
    apply le_of_eq (Eq.symm h')
  · contrapose
    push_neg
    exact le_antisymm h

#check le_of_eq

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩



example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply h₁
    contrapose! h₂
    · apply le_of_eq (Eq.symm h₂)
  · rintro ⟨h₃, h₄⟩
    constructor
    · apply h₃
    contrapose! h₄
    · exact le_antisymm h₃ h₄

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply h₁
    have h₃ : x < y := lt_of_not_ge h₂
    have h₄ : x ≠ y := ne_of_lt h₃
    · exact h₄
  · rintro ⟨h₁', h₂'⟩
    constructor
    · apply h₁'
    push_neg
    have h₃' : x < y := lt_iff_le_and_ne.mpr ⟨h₁', h₂'⟩
    · exact h₃'

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply h₁
    · exact ne_of_lt (lt_of_not_ge h₂)
  · rintro ⟨h₁', h₂'⟩
    constructor
    · apply h₁'
    push_neg
    · exact lt_iff_le_and_ne.mpr ⟨h₁', h₂'⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply h₁
    · exact ne_of_lt (lt_of_not_ge h₂)
  · rintro ⟨h₁', h₂'⟩
    constructor
    · apply h₁'
    · exact not_le_of_gt (lt_iff_le_and_ne.mpr ⟨h₁', h₂'⟩)

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y :=
  ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ne_of_lt (lt_of_not_ge h₂)⟩, fun ⟨h₁', h₂'⟩ ↦ ⟨h₁', not_le_of_gt (lt_iff_le_and_ne.mpr ⟨h₁', h₂'⟩)⟩⟩

#check ne_of_lt
#check not_le_of_lt

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2



theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have hx : 0 ≤ x ^ 2 := by apply pow_two_nonneg
  have hy : 0 ≤ y^2 := by apply pow_two_nonneg
  have hxy : x^2 = 0 ∧ y^2 = 0 := by apply (add_eq_zero_iff_of_nonneg hx hy).1 h
  apply pow_eq_zero hxy.1

theorem aux1 {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have hx : 0 ≤ x ^ 2 := pow_two_nonneg x
  have hy : 0 ≤ y^2 := pow_two_nonneg y
  have hxy : x^2 = 0 ∧ y^2 = 0 := (add_eq_zero_iff_of_nonneg hx hy).1 h
  pow_eq_zero hxy.1

#check pow_two_nonneg
#check add_eq_zero_iff_of_nonneg

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  rintro h
  have hx : 0 ≤ x ^ 2 := pow_two_nonneg x
  have hy : 0 ≤ y^2 := pow_two_nonneg y
  have hxy : x^2 = 0 ∧ y^2 = 0 := (add_eq_zero_iff_of_nonneg hx hy).1 h
  constructor
  · apply pow_eq_zero hxy.1
  · apply pow_eq_zero hxy.2
  rintro ⟨h₁',h₂'⟩
  rw [h₁',h₂']
  norm_num

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  rintro h
  constructor
  · apply aux h
  rw [add_comm] at h
  · apply aux h
  rintro ⟨h₁',h₂'⟩
  rw [h₁',h₂']
  norm_num



section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  intro h
  rw [abs_lt] at h
  constructor
  have h₁ : -5< x + 3 := h.1
  linarith
  have h₂ : x + 3 < 5 := h.2
  linarith

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  rintro ⟨h₁,h₂⟩
  constructor
  linarith
  linarith


example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor
  norm_num
  norm_num

#check Nat.dvd_gcd_iff
end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 1, 2
  norm_num

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 0, 1
  norm_num


section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor
  · intro h
    constructor
    · apply h.1
    · apply Ne.symm (ne_of_not_le h.2)
  · intro h'
    constructor
    · apply h'.1
    apply not_le_of_gt
    · apply lt_of_le_of_ne h'.1 h'.2

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor
  · intro h
    constructor
    · apply h.1
    by_contra h'
    apply h.2
    · exact ge_of_eq h'
  · intro hr
    constructor
    · apply hr.1
    by_contra hr'
    apply hr.2
    · apply le_antisymm hr.1 hr'

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  constructor
  · intro (h : a < b)
    constructor
    · apply (le_of_lt h)
    · apply (ne_of_lt h)
  · intro (h' : a ≤ b ∧ a ≠ b)
    · apply lt_of_le_of_ne h'.1 h'.2

#check le_of_lt
#check lt_of_le_of_ne
#check ne_of_lt
#check Ne.symm
#check ne_of_not_le


end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_ge]
  by_contra h
  apply h.2
  exact h.1


example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  intro h₁
  intro h₂
  constructor
  · apply le_trans h₁.1 h₂.1
  by_contra h'
  apply h₁.2
  · apply le_trans h₂.1 h'



end
