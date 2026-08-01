import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry

theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε (epos : 0 < ε)  (ele1 : ε ≤ 1) (xlt : |x| < ε) (ylt : |y| < ε)
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by apply mul_le_mul; linarith; linarith; apply abs_nonneg; apply abs_nonneg
    _ < 1 * ε := by apply mul_lt_mul; apply lt_of_lt_of_le xlt ele1; linarith; apply epos; linarith;
    _ = ε := by apply one_mul

#check abs_mul
#check mul_le_mul
#check mul_le_mul_left
#check abs_nonneg
#check mul_lt_mul_right
#check mul_lt_mul_left
#check mul_lt_mul
#check one_mul


def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  · apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  · apply hgb


example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  apply mul_nonneg
  · apply nnf
  · apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  dsimp
  apply mul_le_mul
  · apply hfa
  · apply hgb
  · apply nng
  · apply nna

#check mul_le_mul
#check add_le_add
#check mul_nonneg

end


section
variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

example {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  · apply hgb


#check fnUb_add
end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b := by
  intro a b aleb
  apply h
  · apply aleb

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  dsimp
  apply add_le_add
  · apply mf aleb
  · apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b (aleb : a ≤ b)
  dsimp
  apply mul_le_mul_of_nonneg_left
  · apply mf aleb
  · apply nnc

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc


example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b (aleb : a ≤ b)
  dsimp
  apply mf (mg aleb)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb)


def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  dsimp
  calc
    f x * g x = (-f (-x)) * (-g (-x)) := by rw [of, og]
    _ = -((-f (-x)) * g (-x)) := by rw [mul_neg]
    _ = -(-(f (-x) * g (-x))) := by rw [neg_mul]
    _ = f (-x) * g (-x) := by ring


#check mul_neg
#check neg_mul



example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  calc
    f x * g x = f (-x) * (- g (-x)) := by rw [ef, og]
    _ = - (f (-x) * g (-x)) := by rw [mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  calc
   f (g x) = f ( -g (-x)) := by rw [og]
   _ = f (g (-x)) := by rw [← ef]


end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x (xs : x ∈ s)
  exact xs

theorem Subset.refl : s ⊆ s := fun x (xs : x ∈ s) ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro (r_sub_s : r ⊆ s) (s_sub_t : s ⊆ t) (x : α) (x_in_r : x ∈ r)
  apply s_sub_t
  · apply r_sub_s
    · apply x_in_r


end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro (x : α) (x_in_s : x ∈ s)
  apply le_trans
  · apply h
    apply x_in_s
  · apply h'

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  fun x x_in_s ↦ le_trans (h x x_in_s) h'


end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (c_nn : c ≠ 0) : Injective fun x ↦ c * x := by
  intro (x₁ : ℝ) (x₂ : ℝ) (h' : (fun x ↦  c * x) x₁ = (fun x ↦  c * x) x₂)
  apply (mul_right_inj' c_nn).mp h'



#check mul_right_inj'

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro (x₁ : α) (x₂ : α) (h' : (fun x ↦ g (f x)) x₁ = (fun x ↦ g (f x)) x₂)
  have h₀ : (fun x ↦ f x) x₁ = (fun x ↦ f x) x₂ := by
    apply injg h'
  apply injf h₀

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro (x₁ : α) (x₂ : α) (h' : (fun x ↦ g (f x)) x₁ = (fun x ↦ g (f x)) x₂)
  apply injf
  · apply injg h'

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro (x₁ : α) (x₂ : α) (h' : (fun x ↦ g (f x)) x₁ = (fun x ↦ g (f x)) x₂)
  apply injf (injg (h' : (fun x ↦ g (f x)) x₁ = (fun x ↦ g (f x)) x₂))

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro (x₁ : α) (x₂ : α) (h : (fun x ↦ g (f x)) x₁ = (fun x ↦ g (f x)) x₂)
  apply injf (injg h)

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂
  dsimp
  intro  (h : g (f x₁) = g (f x₂))
  apply injf (injg h)

end
