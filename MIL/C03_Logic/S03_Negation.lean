import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a
  apply this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro (fnub : FnHasUb f)
  rcases fnub with ⟨a, fnuba : FnUb f a⟩
  rcases h a with ⟨x₀, hx : f x₀ > a⟩
  have fx : f x₀ ≤ a := fnuba x₀
  have : a < a := lt_of_lt_of_le hx fx
  apply lt_irrefl a
  apply this


example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro (fnlb : FnHasLb f)
  obtain ⟨a, fnlba : FnLb f a⟩ := fnlb
  obtain ⟨x₀, h₀ : f x₀ < a⟩ := h a
  have h₁ : a ≤ f x₀ := fnlba x₀
  have : a < a := lt_of_le_of_lt h₁ h₀
  apply lt_irrefl a
  apply this

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : a ≤ f x := fnlba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro (fnub : FnHasUb fun x ↦ x)
  rcases fnub with ⟨a, fnuba : FnUb (fun x ↦ x) a⟩
  have h₁ : a < a + 1 := by linarith
  have h₂ : (fun x ↦ x) (a + 1) ≤ a := fnuba (a + 1)
  have h₃ : a + 1 ≤ a := h₂
  linarith

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, fnuba : FnUb (fun x ↦ x) a⟩
  have : a + 1 ≤ a := fnuba (a + 1)
  linarith

example : ¬FnHasUb fun (x : ℝ) ↦ (2 + x : ℝ) := by
  intro (fnub : FnHasUb fun (x : ℝ) ↦ (2 + x : ℝ))
  obtain ⟨a, fnuba : FnUb (fun (x : ℝ) ↦ (2 + x : ℝ)) a⟩ := fnub
  have h₂ : a < 2 + a := by linarith
  apply lt_irrefl a
  apply lt_of_lt_of_le h₂ (fnuba a)

example : ¬FnHasUb fun x ↦ x := by
  intro (fnub : FnHasUb fun x ↦ x)
  rcases fnub with ⟨a, fnuba : FnUb (fun x ↦ x) a⟩
  have h₁ : a < a + 1 := by linarith
  have h₂ : a + 1 ≤ a := fnuba (a + 1)
  have h₃ : ¬ a < a + 1 := not_lt_of_ge h₂
  apply h₃
  apply h₁

example : ¬FnHasUb fun x ↦ x := by
  intro (fnub : FnHasUb fun x ↦ x)
  rcases fnub with ⟨a, fnuba : FnUb (fun x ↦ x) a⟩
  have h₁ : a < a + 1 := by linarith
  apply not_lt_of_ge (fnuba (a + 1))
  exact h₁

example : ¬FnHasUb fun x ↦ x := by
  intro (fnub : FnHasUb fun x ↦ x)
  rcases fnub with ⟨a, fnuba : FnUb (fun x ↦ x) a⟩
  apply not_lt_of_ge (fnuba (a + 1))
  linarith



#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro (h₁ : b ≤ a)
  have h₂ : f b ≤ f a := h h₁
  have h₃ : f a < f a := lt_of_lt_of_le h' h₂
  apply lt_irrefl (f a)
  apply h₃

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro (h₁ : b ≤ a)
  apply lt_irrefl (f a)
  apply lt_of_lt_of_le h' (h h₁)


example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro (mf : Monotone f)
  have h₁ : f a ≤ f b := mf h
  have : f a < f a := lt_of_le_of_lt h₁ h'
  apply lt_irrefl (f a)
  apply this

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro (mf : Monotone f)
  apply lt_irrefl (f a)
  apply lt_of_le_of_lt (mf h) h'

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro (mf : Monotone f)
  apply absurd h'
  apply not_lt_of_ge
  apply mf h

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro (mf : Monotone f)
  have h₁ : f a ≤ f b := mf h
  have h₂ : ¬ f b < f a := not_lt_of_ge h₁
  apply h₂
  exact h'

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro (monof : Monotone f)
  apply not_lt_of_ge (monof h)
  exact h'


example : Monotone fun (x : ℝ) ↦ (0 : ℝ) := by
  intro a b (aleb : a ≤ b)
  dsimp
  apply le_refl

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro (h : ∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b : ℝ}, f a ≤ f b → a ≤ b)
  let f := fun (x : ℝ) ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b (aleb : a ≤ b)
    apply le_refl
  have f1lef0 : f 1 ≤ f 0 := le_refl _
  have h₂ : (1 : ℝ) ≤ (0 : ℝ) := h monof f1lef0
  have h₃ : ¬ (1 : ℝ) ≤ (0 : ℝ) := by linarith
  apply h₃
  exact h₂

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro (h : ∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b : ℝ}, f a ≤ f b → a ≤ b)
  let f := fun (x : ℝ) ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b (aleb : a ≤ b)
    apply le_refl
  have f1lef0 : f 1 ≤ f 0 := le_refl _
  have : (0 : ℝ) < (1 : ℝ) := by linarith
  apply not_le_of_gt this
  exact h monof f1lef0


example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro (nlx : 0 < x)
  have h₁ : ∃ ε : ℝ, 0 < ε ∧  ε < x := ⟨x / 2, by norm_num [nlx]⟩
  rcases h₁ with ⟨a, ax : (0 < a ∧ a < x)⟩
  have h₂ : x < a := h _

 example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro (nlx : 0 < x)
  have h₁ : 0 < x / 2 := by norm_num [nlx]
  have h₂ : x < x / 2 := by
    apply h
    apply h₁
  have h₃ : x / 2 ≤  x := by linarith
  have h₄ : x < x := lt_of_lt_of_le h₂ h₃
  apply lt_irrefl x
  apply h₄

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro (nlx : 0 < x)
  have h₁ : 0 < x / 2 := by norm_num [nlx]
  have h₂ : x < x / 2 := by
    apply h
    apply h₁
  have h₃ : x / 2 ≤  x := by linarith
  apply not_le_of_gt h₂
  exact h₃


example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro (nlx : 0 < x)
  linarith [h _ nlx]

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x : α, P x) : ∀ x, ¬P x := by
  intro (y: α) (py : P y)
  apply h
  use y

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro (px : ∃ x : α, P x)
  rcases px with ⟨y, py : P y⟩
  have : ¬ P y := h y
  apply this
  exact py

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, Px⟩
  exact h x Px

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨y : α, py : P y⟩
  apply h y
  exact py

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra nex
  apply h
  intro (y : α)
  show P y
  by_contra npy
  apply nex
  use y



example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro (axP : ∀ x : α, P x)
  rcases h with ⟨y : α, nPy : ¬ P y⟩
  apply nPy
  exact axP y

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, nPx⟩
  apply nPx
  apply h'


example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra nq
  apply h
  show ¬ Q
  exact nq


example (h : Q) : ¬¬Q := by
  intro (h' : ¬ Q)
  apply h'
  show Q
  exact h



end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro (a : ℝ)
  by_contra h'
  apply h
  use a
  intro (x : ℝ)
  apply le_of_not_gt
  by_contra h''
  apply h'
  use x


example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro (a : ℝ)
  by_contra h'
  apply h
  use a
  intro (x : ℝ)
  apply le_of_not_gt
  intro (h'' : a < f x)
  apply h'
  use x


example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  by_contra h'
  have h₁ : ∀ a, ∃ x, f x > a := by
    intro (a : ℝ)
    by_contra h''
    apply h'
    use a
    intro (x : ℝ)
    apply le_of_not_gt
    intro (h''' : a < f x)
    apply h''
    use x
  apply h
  exact h₁


example (h : ¬FnHasUb (f : ℝ → ℝ)) : ∀ (a : ℝ), ∃ (x : ℝ), f x > a := by
  dsimp only [FnHasUb] at h
  dsimp only [FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone (f : ℝ → ℝ)) : ∃ (x y : ℝ), x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  exact h


example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb] at h
  dsimp only [FnUb] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb] at h
  dsimp only [FnUb] at h
  contrapose h
  push_neg at h
  push_neg
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb] at h
  dsimp only [FnUb] at h
  contrapose! h
  exact h



example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose h
  push_neg at h
  push_neg
  use x / 2
  have h₁ : x / 2 > 0  := by norm_num [h]
  have h₂ : x / 2 < x := by linarith
  constructor
  · apply h₁
  · apply h₂



end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  show False
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

example (h : 0 < 0) : a > 37 := by
  contrapose h
  have h' : ¬0 < 0 := lt_irrefl 0
  exact h'

example (h : 0 < 0) : a > 37 := by
  contrapose h
  show ¬ 0 < 0
  exact lt_irrefl 0

example (h : 0 < 0) : a > 37 := by
  contrapose! h
  have : 0 ≤ 0 := le_refl 0
  exact this

example (h : 0 < 0) : a > 37 := by
  contrapose! h
  show 0 ≤ 0
  exact le_refl 0

example (h : 0 < 0) : a > 37 := by
  by_contra h'
  show False
  exfalso
  show False
  apply lt_irrefl 0 h




end
