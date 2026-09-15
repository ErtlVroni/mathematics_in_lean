import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases (le_or_gt 0 y) with (h : 0 ≤ y) | (h' : y < 0)
  · rw [abs_of_nonneg h]
    intro (h1 : x < y)
    left
    exact h1
  · rw [abs_of_neg h']
    intro (h1' : x < -y)
    right
    exact h1'

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h₁
    left
    exact h₁
  case inr h =>
    rw [abs_of_neg h]
    intro h₁
    right
    exact h₁

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases (le_or_gt 0 x) with (h : 0 ≤ x) | (h' : x < 0)
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h']
    linarith

theorem le_abs_self1 (x : ℝ) : x ≤ |x| := by
  rcases (le_or_gt 0 x) with (h : 0 ≤ x) | (h' : x < 0)
  have h1 : |x| = x :=  (abs_of_nonneg h)
  have h2 : x ≤ |x| := ge_of_eq h1
  · exact h2
  have h1' : 0 ≤ |x| := (abs_nonneg x)
  have h2' : x < |x| := (lt_of_lt_of_le h' h1')
  have h3' : x ≤ |x| := le_of_lt h2'
  · exact h3'

theorem le_abs_self2 (x : ℝ) : x ≤ |x| := by
  rcases (le_or_gt 0 x) with (h : 0 ≤ x) | (h' : x < 0)
  · exact ge_of_eq (abs_of_nonneg h)
  · exact le_of_lt (lt_of_lt_of_le h' (abs_nonneg x))

#check le_refl
#check ge_of_eq
#check abs_nonneg
#check lt_of_le_of_lt
#check le_of_lt
#check abs_neg

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  have h : -x ≤ |-x| := le_abs_self (-x)
  have h' : |-x| = |x| := (abs_neg x)
  rw [h'] at h
  exact h

theorem neg_le_abs_self1 (x : ℝ) : -x ≤ |x| := by
  have h : -x ≤ |-x| := le_abs_self (-x)
  rw [(abs_neg x)] at h
  exact h

theorem neg_le_abs_self2 (x : ℝ) : -x ≤ |x| := by
  have h : -x ≤ |-x| := (le_abs_self (-x))
  have h' : |-x| = |x| := (abs_neg x)
  have h'' : -x ≤ |x| := (le_of_le_of_eq h h')
  · exact h''

theorem neg_le_abs_self3 (x : ℝ) : -x ≤ |x| :=
  le_of_le_of_eq (le_abs_self (-x)) (abs_neg x)


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases (le_or_gt 0 (x+y)) with (h : 0 ≤ (x+y)) | (h' : (x+y) < 0)
  have h1 : |x + y|= x + y := abs_of_nonneg h
  rw [h1]
  have h2 : x ≤ |x| ∧ y ≤ |y| := ⟨le_abs_self x, le_abs_self y⟩
  · apply add_le_add h2.1 h2.2
  have h1' : |x + y| = -(x + y) := abs_of_neg h'
  rw [h1']
  rw [neg_add]
  have h2' : -x ≤ |x| ∧ -y ≤ |y| := ⟨neg_le_abs_self x, neg_le_abs_self y⟩
  · apply add_le_add h2'.1 h2'.2

#check add_le_add
#check neg_add

example : |x + y| ≤ |x| + |y| := by
  rcases (le_or_gt 0 (x+y)) with (h : 0 ≤ (x+y)) | (h' : (x+y) < 0)
  have h1 : |x + y|= x + y := abs_of_nonneg h
  have h2 : x + y ≤ |x| + |y| :=  add_le_add (le_abs_self x) (le_abs_self y)
  · apply le_of_eq_of_le h1 h2
  have h1' : |x + y| = -(x + y) := abs_of_neg h'
  have h2' : -x ≤ |x| ∧ -y ≤ |y| := ⟨neg_le_abs_self x, neg_le_abs_self y⟩
  have h3' : -x + -y ≤ |x| + |y| := add_le_add h2'.1 h2'.2
  have h4' : -(x+y) = -x +-y := neg_add x y
  have h5' : |x + y| = -x +-y := Eq.trans h1' h4'
  have h6' : |x + y| ≤ |x| + |y| := le_of_eq_of_le h5' h3'
  · exact h6'

example : |x + y| ≤ |x| + |y| := by
  rcases (le_or_gt 0 (x+y)) with (h : 0 ≤ (x+y)) | (h' : (x+y) < 0)
  · apply le_of_eq_of_le (abs_of_nonneg h) (add_le_add (le_abs_self x) (le_abs_self y))
  · exact le_of_eq_of_le (Eq.trans (abs_of_neg h') (neg_add x y)) (add_le_add (neg_le_abs_self x) (neg_le_abs_self y))



theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  rcases (le_or_gt 0 y) with (h : 0 ≤ y) | (h' : y < 0)
  · have h1 : |y| = y := abs_of_nonneg h
    intro h2
    rw [h1] at h2
    left
    exact h2
  · have h1' : |y| = -y := abs_of_neg h'
    intro h2'
    rw [h1'] at h2'
    right
    exact h2'
  intro h
  rcases h with h' | h''
  · have h1' : y ≤ |y| := le_abs_self y
    have h2' : x < |y| := lt_of_lt_of_le h' h1'
    apply h2'
  · have h1'' : -y ≤ |y| := neg_le_abs_self y
    have h2'' : x < |y| := lt_of_lt_of_le h'' h1''
    apply h2''

example : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · rcases (le_or_gt 0 y) with (h : 0 ≤ y) | (h' : y < 0)
    intro h2
    left
    · apply lt_of_lt_of_eq h2 (abs_of_nonneg h)
    intro h2'
    right
    · apply lt_of_lt_of_eq h2' (abs_of_neg h')
  · intro h
    rcases h with h' | h''
    · apply lt_of_lt_of_le h' (le_abs_self y)
    · apply lt_of_lt_of_le h'' (neg_le_abs_self y)



theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases (le_or_gt 0 x) with (h : 0 ≤ x) | (h' : x < 0)
  · rw [abs_of_nonneg h]
    constructor
    · intro hxy
      constructor
      · have h1 : 0 < y := lt_of_le_of_lt h hxy
        have h2 : -y < 0 := neg_neg_of_pos h1
        have h3 : -y < x := lt_of_lt_of_le h2 h
        exact h3
      · exact hxy
    · intro hyxxy
      · exact hyxxy.2
  · rw [abs_of_neg h']
    constructor
    · intro hmxy
      constructor
      · have h1' : -y < x := neg_lt.2 hmxy
        exact h1'
      · have h2' : 0 < -x := neg_pos_of_neg h'
        have h3' : 0 < y := lt_trans h2' hmxy
        have h4' : x < y := lt_trans h' h3'
        exact h4'
    · intro hmyxxy
      · have h5' : -x < y := neg_lt.1 hmyxxy.1
        exact h5'

example : |x| < y ↔ -y < x ∧ x < y := by
  rcases (le_or_gt 0 x) with (h : 0 ≤ x) | (h' : x < 0)
  · rw [abs_of_nonneg h]
    constructor
    · intro (hxy : x < y)
      constructor
      · exact lt_of_lt_of_le (neg_neg_of_pos (lt_of_le_of_lt h hxy)) h
      · exact hxy
    · intro (hyxxy : -y < x ∧ x < y)
      · exact hyxxy.2
  · rw [abs_of_neg h']
    constructor
    · intro (hmxy : -x < y)
      constructor
      · exact neg_lt.2 hmxy
      · exact lt_trans h' (lt_trans (neg_pos_of_neg h') hmxy)
    · intro (hmyxxy : -y < x ∧ x < y)
      · exact neg_lt.1 hmyxxy.1


#check neg_lt
#check neg_of_neg_pos
#check neg_neg_of_pos


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right
    exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc m a k]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a,  m | n⟩ | ⟨b, m | k⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm n (m * b), mul_assoc m b n]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, (h₁ : z = x^2 + y^2) | (h₂ : z = x^2 + y^2 + 1)⟩
  · have hx₁ : x^2 ≥ 0 := pow_two_nonneg x
    have hy₁ : y^2 ≥ 0 := pow_two_nonneg y
    have hxy₁ : x^2 + y^2 ≥ 0 := add_nonneg hx₁ hy₁
    have hxyz₁ : z ≥ x^2 + y^2 := ge_of_eq h₁
    have hz₁ : z ≥ 0 := le_trans hxy₁ hxyz₁
    exact hz₁
  · have hx₂ : x^2 ≥ 0 := pow_two_nonneg x
    have hy₂ : y^2 ≥ 0 := pow_two_nonneg y
    have hxy1 : x^2 + y^2 + 1 ≥ 0 := by linarith
    have hxyz₂ : z ≥ x^2 + y^2 + 1 := ge_of_eq h₂
    have hz₂ : z ≥ 0 := le_trans hxy1 hxyz₂
    exact hz₂

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, (h₁ : z = x^2 + y^2) | (h₂ : z = x^2 + y^2 + 1)⟩
  · have hx₁ : x^2 ≥ 0 := pow_two_nonneg x
    have hy₁ : y^2 ≥ 0 := pow_two_nonneg y
    have hxy₁ : x^2 + y^2 ≥ 0 := add_nonneg hx₁ hy₁
    have hz₁ : z ≥ 0 := le_of_le_of_eq hxy₁ (symm h₁)
    exact hz₁
  · have hx₂ : x^2 ≥ 0 := pow_two_nonneg x
    have hy₂ : y^2 ≥ 0 := pow_two_nonneg y
    have hxy1 : x^2 + y^2 + 1 ≥ 0 := by linarith
    have hz₂ : z ≥ 0 := le_of_le_of_eq hxy1 (symm h₂)
    exact hz₂

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]


#check pow_two_nonneg
#check add_nonneg
#check le_of_le_of_eq
#check le_of_eq_of_le
#check ge_of_eq




example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : x^2 - 1 = 0 := by rw[h, sub_self 1]
  have h2 : (x + 1)*(x-1) = 0 := by rw[← h1]; ring
  have h3 : (x + 1) = 0 ∨ (x - 1) = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  rcases h3 with h3p | h3m
  · right
    apply eq_neg_iff_add_eq_zero.2 h3p
  · left
    apply eq_of_sub_eq_zero h3m

#check eq_zero_or_eq_zero_of_mul_eq_zero
#check eq_neg_iff_add_eq_zero
#check eq_of_sub_eq_zero


example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1 : x^2 - y^2 = 0 := by rw[h, sub_self]
  have h2 : (x + y)*(x - y) = 0 := by rw[← h1]; ring
  have h3 : (x + y) = 0 ∨ (x - y) = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  rcases h3 with (h3p : x + y = 0) | (h3m : x - y = 0)
  · right
    apply eq_neg_iff_add_eq_zero.2 h3p
  · left
    apply eq_of_sub_eq_zero h3m

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : x^2 - 1 = 0 := by rw [h, sub_self 1]
  have h2 : (x - 1)*(x + 1) = 0 := by rw [← h1]; ring
  rcases (eq_zero_or_eq_zero_of_mul_eq_zero h2) with h3 | h3'
  · left
    apply eq_of_sub_eq_zero h3
  · right
    apply eq_neg_iff_add_eq_zero.2 h3'


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1 : x^2 - y^2 = 0 := by rw[h, sub_self]
  have h2 : (x - y)*(x + y) = 0 := by rw[← h1]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with (h3 : x - y = 0) | (h3' : x + y = 0)
  · left
    apply eq_of_sub_eq_zero h3
  · right
    apply eq_neg_iff_add_eq_zero.2 h3'


end

#check em

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    cases em P
    · right
      apply h
      assumption
    · left
      assumption
  · intro h'
    rcases h' with h1' |  h2'
    · contrapose
      intro h3'
      apply h1'
    · intro h4'
      apply h2'


example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    rcases em P with h1 | h2
    · right
      exact h h1
    · left
      exact h2
  rintro (h1' | h2')
  · intro h3'
    exact absurd h3' h1'
  · intro h4'
    exact h2'

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      exact h h'
    · left
      exact h'
  rintro (h | h)
  · intro h'
    exact absurd h' h
  · intro
    exact h
