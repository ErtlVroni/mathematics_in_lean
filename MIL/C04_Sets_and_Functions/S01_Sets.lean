import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

#check α
#check s
#check s ∪ t
#check s ∩ t

variable (x : s)
#check x
#check ∅
#check univ

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨(xs : x ∈ s), (xu : x ∈ u)⟩ ↦ ⟨(h xs : x ∈ t), (xu : x ∈ u)⟩

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  intro (x : α) (hx : x ∈ s ∩ (t ∪ u))
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases (xtu : x ∈ t ∪ u) with (xt : x ∈ t) | (xu : x ∈ u)
  · left
    show x ∈ s ∩ t
    exact ⟨(xs : x ∈ s), (xt : x ∈ t)⟩
  · right
    show x ∈ s ∩ u
    exact ⟨(xs : x ∈ s), (xu : x ∈ u)⟩

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  rintro (x : α) ⟨(xs : x ∈ s), (xt : x ∈ t) | (xu : x ∈ u)⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  rintro (x : α) ((xst : x ∈ s ∩ t) | (xsu : x ∈ s ∩ u))
  · have xs : x ∈ s := xst.1
    have xt : x ∈ t := xst.2
    have xtu : x ∈ (t ∪ u) := by left; exact xt
    exact ⟨xs, xtu⟩
  · have xs : x ∈ s := xsu.1
    have xu : x ∈ u := xsu.2
    have xtu : x ∈ (t ∪ u) := by right; exact xu
    exact ⟨xs, xtu⟩

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  rintro (x : α) ((xst : x ∈ s ∩ t) | (xsu : x ∈ s ∩ u))
  · exact ⟨xst.1, Or.inl xst.2⟩
  · exact ⟨xsu.1, (Or.inr xsu.2)⟩

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  intro (x : α) (h: x ∈ (s ∩ t) ∪ (s ∩ u))
  have xs : x ∈ s := by
    rcases h with (xst | xsu)
    · exact xst.1
    · exact xsu.1
  use xs
  show x ∈ t ∪ u
  rcases h with (xst | xsu)
  · left; exact xst.2
  · right; exact xsu.2

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  rintro (x : α) (⟨(xs : x ∈ s), (xt : x ∈ t)⟩ | ⟨(xs : x ∈ s), (xu : x ∈ u)⟩)
  · use xs
    show x ∈ t ∪ u
    left; exact xt
  · use xs
    show x ∈ t ∪ u
    right; exact xu


example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  rintro (x : α) (⟨(xs : x ∈ s), (xt : x ∈ t)⟩ | ⟨(xs : x ∈ s), (xu : x ∈ u)⟩)
  · exact ⟨xs, Or.inl xt⟩
  · exact ⟨xs, Or.inr xu⟩


example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro (x : α) ⟨⟨(xs : x ∈ s), (xnt : x ∉ t)⟩, (xnu : x ∉ u)⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro (x : α) ⟨⟨(xs : x ∈ s), (xnt : x ∉ t)⟩, (xnu : x ∉ u)⟩
  use xs
  rintro (xt | xu)
  · apply xnt
    exact xt
  · apply xnu
    exact xu


example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro (x : α) ⟨(xs : x ∈ s), (xntu : x ∉ (t ∪ u))⟩
  have xnt : x ∉ t := by
    intro xt
    have xtu : x ∈ t ∪ u := by left; exact xt
    apply xntu; exact xtu
  have xnu : x ∉ u := by
    intro xu
    have xtu : x ∈ t ∪ u := by right; exact xu
    apply xntu; exact xtu
  exact ⟨⟨xs, xnt⟩, xnu⟩


example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  use xs
  · intro xt
    exact xntu (Or.inl xt)
  · intro xu
    apply xntu (Or.inr xu)

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  · constructor
    · exact xs
    · intro xt; exact xntu (Or.inl xt)
  · intro xu; exact xntu (Or.inr xu)


example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) (fun x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩)


example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm
  · show s ∩ (s ∪ t) ⊆  s
    rintro x ⟨xs, xst⟩
    exact xs
  · show s ⊆ s ∩ (s ∪ t)
    rintro x xs
    constructor
    · exact xs
    · left; exact xs

example : s ∩ (s ∪ t) = s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xst⟩
    exact xs
  · rintro xs
    exact ⟨xs, Or.inl xs⟩

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  · rintro ⟨xs, xst⟩
    exact xs
  · rintro xs
    exact ⟨xs, Or.inl xs⟩

example : s ∩ (s ∪ t) = s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xst⟩ ↦ xs, fun xs ↦ ⟨xs, Or.inl xs⟩⟩

example : s ∩ (s ∪ t) = s :=
  Subset.antisymm (fun x ⟨xs, xst⟩ ↦ xs) (fun x xs ↦ ⟨xs, Or.inl xs⟩)

example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  · show s ∪ (s ∩ t) ⊆ s
    rintro x ((xs : x ∈ s) | (xst : x ∈ s ∩ t))
    · exact xs
    · exact xst.1
  · show s ⊆ s ∪ (s ∩ t)
    rintro x (xs : x ∈ s)
    left; exact xs

example : s ∪ s ∩ t = s := by
  ext x
  constructor
  · rintro ((xs : x ∈ s) | (xst : x ∈ s ∩ t))
    · exact xs
    · exact xst.1
  · rintro (xs : x ∈ s)
    left; exact xs



example : (s \ t) ∪ t = s ∪ t := by
  apply Subset.antisymm
  · show s \ t ∪ t ⊆ s ∪ t
    rintro x (⟨(xs : x ∈ s), (xnt : x ∉ t)⟩ | (xt : x ∈ t))
    · left; exact xs
    · right; exact xt
  · show s ∪ t ⊆ (s \ t) ∪ t
    rintro x ((xs : x ∈ s) | (xt : x ∈ t))
    · by_cases h : x ∈ t
      · right; exact h
      · left; exact ⟨xs, h⟩
    · right; exact xt

example : (s \ t) ∪ t = s ∪ t := by
  apply Subset.antisymm
  · show s \ t ∪ t ⊆ s ∪ t
    rintro x (⟨(xs : x ∈ s), (xnt : x ∉ t)⟩ | (xt : x ∈ t))
    · left; exact xs
    · right; exact xt
  · show s ∪ t ⊆ (s \ t) ∪ t
    rintro x ((xs : x ∈ s) | (xt : x ∈ t))
    · cases em (x ∈ t)
      · right; assumption
      · have h : x ∉ t := by assumption
        left; exact ⟨xs, h⟩
    · right; exact xt



example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Subset.antisymm
  · show s \ t ∪ t \ s ⊆ (s ∪ t) \ (s ∩ t)
    rintro x (⟨(xs : x ∈ s), (xnt : x ∉ t)⟩ | ⟨(xt : x ∈ t), (xns : x ∉ s)⟩)
    · have xst : x ∈ s ∪ t := by left; exact xs
      have xnst : x ∉ s ∩ t := by
        intro h
        apply xnt; exact h.2
      exact ⟨xst, xnst⟩
    · have xts : x ∈ s ∪ t := by right; exact xt
      have xnts : x ∉ s ∩ t := by
        intro h
        apply xns; exact h.1
      exact ⟨xts, xnts⟩
  · show (s ∪ t) \ (s ∩ t) ⊆ s \ t ∪ t \ s
    rintro y ⟨((ys : y ∈ s) | (yt : y ∈ t)), (ynst : y ∉ s ∩ t)⟩
    · left
      use ys
      intro h
      apply ynst
      exact ⟨ys, h⟩
    · right
      use yt
      intro h
      apply ynst
      exact ⟨h, yt⟩



def evens : Set ℕ :=
  { n | Even n }

#check ℕ
#check Set ℕ
#check Set
#check evens
#check em
#check Classical.em


def odds : Set ℕ :=
  { n | ¬Even n }

#check odds
#check univ

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example : evens ∪ odds = univ := by
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em (n ∈ evens)

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False := by
  apply h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example (x : ℕ)  (h : x ∈ (univ : Set ℕ)) : True := by
  trivial



example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  rintro n ⟨np: Nat.Prime n, ng2 : n>2⟩
  simp
  rcases Nat.Prime.eq_two_or_odd np with neq2 | nodd
  · rw [neq2]
    linarith
  · rw [Nat.odd_iff, nodd]

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  rintro n ⟨np: Nat.Prime n, ng2 : n>2⟩
  dsimp
  by_contra h
  rcases Nat.Prime.eq_two_or_odd np with neq2 | nodd
  · have h1 : 2 > 2 := by apply lt_of_lt_of_eq ng2 neq2
    apply lt_irrefl 2; apply h1
  · have h2 : n % 2 = 0 := by apply Nat.even_iff.1 h
    rw [nodd] at h2
    sorry





#check Nat.odd_iff
#check Nat.even_iff
#check ZMod.val_ne_zero





#check Nat.Prime.eq_two_or_odd
#check lt_of_lt_of_eq


#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Nat.Prime n) : Prime n := by
  rw [Nat.prime_iff] at h
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  assumption

example (n : ℕ) (h : Nat.Prime n) : Prime n := by
  rw [Nat.prime_iff] at h
  assumption

example (n : ℕ) (h : Nat.Prime n) : Prime n := by
  rwa [Nat.prime_iff] at h


end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro (x : ℕ) (xs : x ∈ s)
  constructor
  · apply h₀ x xs
  · apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨(x : ℕ), (xs : x ∈ s), (nex : ¬Even x), (prime_x : Prime x)⟩
  use x

section
variable (ssubt : s ⊆ t)

#check ssubt

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro (x : ℕ) (xs : x ∈ s)
  have h : x ∈ t := by apply ssubt xs
  constructor
  · apply h₀ x h
  · apply h₁ x h

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨(x : ℕ), (xs : x ∈ s), (nex : ¬Even x), (px : Prime x)⟩
  have h : x ∈ t := by apply ssubt xs
  use x

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

#check ⋃ i, A i

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  · rintro ⟨i, xAi, xs⟩
    exact ⟨xs, ⟨i, xAi⟩⟩


example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    · intro i
      exact (h i).2
  · rintro ⟨h1, h2⟩ i
    constructor
    · exact h1 i
    · exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro ((xs : x ∈ s) | (h : ∀ (i : I), x ∈ A i))
    · intro i
      right; exact xs
    · intro i
      left; exact h i
  · intro h
    by_cases xs : x ∈ s
    · left; exact xs
    · right
      intro i
      cases h i
      · assumption
      · contradiction



def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
