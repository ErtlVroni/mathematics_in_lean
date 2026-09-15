import MIL.Common
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace C03S02

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

#check ∃ x : ℝ, 2 < x ∧ x < 3

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

theorem fnLb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnLb f a) (hgb : FnLb g b) :
    FnLb (fun x ↦ f x + g x) (a  + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  · apply hgb

section

variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa : FnLb f a⟩
  rcases lbg with ⟨b, lbgb : FnLb g b⟩
  use a + b
  apply fnLb_add lbfa lbgb

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa : FnLb f a⟩
  rcases lbg with ⟨b, lbgb : FnLb g b⟩
  use a + b
  apply fun x ↦ add_le_add (lbfa x) (lbgb x)


example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa : FnUb f a⟩
  use c * a
  apply fun x ↦ mul_le_mul_of_nonneg_left (ubfa x) h

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa : FnUb f a⟩
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (ubfa x) h

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa : FnUb f a⟩
  use c * a
  intro x
  dsimp
  apply mul_le_mul_of_nonneg_left
  · apply (ubfa x)
  · apply h

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  obtain ⟨a, ubfa : FnUb f a⟩ := ubf
  exact ⟨c * a, fun x ↦ mul_le_mul_of_nonneg_left (ubfa x) h⟩

#check mul_le_mul_of_nonneg_left


example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

end

example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩

section

variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq : x = a^2 + b^2⟩
  rcases sosy with ⟨c, d, yeq : y = c^2 + d^2⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

theorem sumOfSquares_mul3 {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) : SumOfSquares (x * y) := by
  obtain ⟨a, b, xeq : x = a^2 + b^2⟩ := sosx
  obtain ⟨c, d, yeq : y = c^2 + d^2⟩ := sosy
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

end

section
variable {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq : b = a * d⟩
  rcases divbc with ⟨e, ceq : c = b * e⟩
  rw [ceq, beq]
  use d * e;
  ring

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩
  rcases divbc with ⟨e, rfl⟩
  use d * e
  ring


example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq : b = a * d⟩
  rcases divbc with ⟨e, ceq : c = b * e⟩
  rw [ceq, beq]
  rw [mul_assoc]
  use d * e

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  obtain ⟨d, beq : b = a * d⟩ := divab
  obtain ⟨e, ceq : c = a * e⟩ := divac
  rw [beq, ceq]
  rw [← mul_add]
  use (d + e)

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, beq : b = a * d⟩
  rcases divac with ⟨e, ceq : c = a * e⟩
  rw [beq, ceq]
  rw [← mul_add]
  use (d + e)

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, beq : b = a * d⟩
  rcases divac with ⟨e, ceq : c = a * e⟩
  rw [beq, ceq]
  use (d + e)
  ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩
  rcases divac with ⟨e, rfl⟩
  rw [← mul_add]
  use (d + e)

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  obtain ⟨d, rfl⟩ := divab
  obtain ⟨e, rfl⟩ := divac
  use (d + e)
  rw [← mul_add]


#check add_mul
#check mul_add
end

section

open Function

example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro (y : ℝ)
  use y / c
  dsimp
  rw [mul_div_cancel₀ y h]

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro (y : ℝ)
  use y / c
  dsimp
  field_simp [h]




example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx : f x = 2⟩
  use x
  rw [hx]
  norm_num

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx : f x = 2⟩
  use x
  rw [hx]
  ring

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  obtain ⟨a, ha : f a = -2⟩ :=  h (-2)
  use a
  rw [ha]
  ring

end

section
open Function
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro (c : γ)
  rcases surjg c with ⟨b, gbc : g b = c⟩
  rcases surjf b with ⟨a, fab : f a = b⟩
  use a
  dsimp
  rw [fab, gbc]

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro (c : γ)
  dsimp
  rcases surjg c with ⟨b, rfl⟩
  rcases surjf b with ⟨a, rfl⟩
  use a



end
