import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

def ConvergesTo' (s : ℕ → ℝ) (a : ℝ) :=
  ∀ (ε : ℝ), ε > 0 → ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext u v
  ring

example : (fun x : ℝ ↦ x + 1) = (fun x : ℝ ↦ 1 + x) := by
  ext a
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  · exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

example (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro (ε : ℝ) (εpos : ε > 0)
  use 0
  intro (n : ℕ) (nge : n ≥ 0)
  dsimp
  rw [sub_self, abs_zero]
  exact εpos


theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro (ε : ℝ) (εpos : ε > 0)
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns : ℕ, hs :  ∀ n ≥ Ns, |s n - a| < ε / 2⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt : ℕ, ht :  ∀ n ≥ Nt, |t n - b| < ε / 2⟩
  use max Ns Nt
  intro n (hn : n ≥ max Ns Nt)
  have ngeNs : n ≥ Ns := le_of_max_le_left hn
  have ngeNt : n ≥ Nt := le_of_max_le_right hn
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := by
      apply abs_add (s n - a) (t n -b)
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add (hs n ngeNs) (ht n ngeNt)
    _ = ε := by norm_num



theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  sorry

example {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  rcases (eq_or_ne c 0) with (h : c = 0) | (h' : c ≠ 0)
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  · have acpos : 0 < |c| := abs_pos.mpr h'
    intro (ε : ℝ) (epos : ε > 0)
    dsimp
    have ecpos : 0 < ε / |c| := by apply div_pos epos acpos
    rcases cs (ε / |c|) ecpos with ⟨Ns : ℕ, hs :  ∀ n ≥ Ns, |s n - a| < ε / |c|⟩
    use Ns
    intro n (hn : n ≥ Ns)
    calc
      |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
      _ < |c| * (ε / |c|) := by apply (mul_lt_mul_of_pos_left (hs n hn) acpos)
      _ = ε := mul_div_cancel₀ ε (ne_of_lt acpos).symm

example {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  rcases (eq_or_ne c 0) with (h : c = 0) | (h' : c ≠ 0)
  · intro (ε : ℝ) (epos : ε > 0)
    dsimp
    rcases cs ε epos with ⟨Ns : ℕ, hs :  ∀ n ≥ Ns, |s n - a| < ε⟩
    use Ns
    intro n (hn : n ≥ Ns)
    calc
      |c * s n - c * a| = |c * (s n -a)| := by
        congr
        ring
      _ = |0 * (s n - a)| := by rw [h]
      _ = |0| := by
        congr
        ring
      _ = 0 := by apply abs_zero
      _ < ε := epos
  · have acpos : 0 < |c| := abs_pos.mpr h'
    intro (ε : ℝ) (epos : ε > 0)
    dsimp
    have ecpos : 0 < ε / |c| := by apply div_pos epos acpos
    rcases cs (ε / |c|) ecpos with ⟨Ns : ℕ, hs :  ∀ n ≥ Ns, |s n - a| < ε / |c|⟩
    use Ns
    intro n (hn : n ≥ Ns)
    calc
      |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
      _ < |c| * (ε / |c|) := by apply (mul_lt_mul_of_pos_left (hs n hn) acpos)
      _ = ε := mul_div_cancel₀ ε (ne_of_lt acpos).symm


#check eq_or_ne
#check add_zero

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N : ℕ, h : ∀ n ≥ N, |s n - a| < 1⟩
  use (N : ℕ), |a| + 1
  intro n (hn : n ≥ N)
  calc
    |s n| = |s n - a + a| := by
      congr
      ring
    _ ≤ |s n - a| + |a| := by
      apply abs_add (s n - a) a
    _ < 1 + |a| := by apply add_lt_add_right (h n hn) |a|
    _ = |a| + 1 := by apply add_comm


theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro (ε : ℝ) (epos : ε > 0)
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨(N₀ : ℕ), (B : ℝ), (h₀ : ∀ (n : ℕ), N₀ ≤ n → |s n| < B)⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg (s N₀)) (h₀ N₀ (le_refl N₀))
  have pos₀ : ε / B > 0 := div_pos epos Bpos
  rcases ct (ε / B) pos₀ with ⟨(N₁ : ℕ), (h₁: ∀ n ≥ N₁, |t n - 0| < ε / B)⟩
  use max N₀ N₁
  intro n (hn : n ≥ max N₀ N₁)
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left hn
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right hn
  calc
    |s n * t n - 0| = |s n * t n| := by congr; ring
    _ = |s n| * |t n| := by apply abs_mul
    _ = |s n| * |t n - 0| := by congr; ring
    _ < B * (ε / B) := by apply mul_lt_mul'' (h₀ n ngeN₀) (h₁ n ngeN₁) (abs_nonneg (s n)) (abs_nonneg (t n - 0))
    _ = ε := by apply mul_div_cancel₀ ε (ne_of_lt Bpos).symm

#check mul_lt_mul_of_lt_of_lt
#check mul_lt_mul
#check le_of_lt
#check mul_lt_mul''



theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert this using 1
  · ext; ring
  ring

example {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ (t n + -b)) 0 := by
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have h₂ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs h₁
  have h₃ : ConvergesTo (fun n ↦ s n * (t n + -b) + b * s n) (0 + b * a) := by
    apply convergesTo_add h₂ (convergesTo_mul_const b cs)
  convert h₃ using 1
  · ext; ring
  ring

#check sub_self

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) : a = b := by
  by_contra abne
  have ambpos : |a - b| > 0 := by
    rcases (lt_or_gt_of_ne abne) with (h : a < b) | (h' : b < a)
    · have h₁ : a - b < 0 := by linarith
      have h₂ : -(a - b) = |a - b| := by apply (abs_of_neg h₁).symm
      have h₃ : b - a = -(a - b) := by ring
      have h₄ : b - a > 0 := by linarith
      have h₅ : -(a - b) > 0 := by apply lt_of_lt_of_eq h₄ h₃
      have h₆ : |a - b| > 0 := by apply lt_of_lt_of_eq h₅ h₂
      exact h₆
    · have h₁' : a - b > 0 := by linarith
      have h₂' : a - b = |a - b| := by apply (abs_of_pos h₁').symm
      have h₃' : |a - b| > 0 := by apply lt_of_lt_of_eq h₁' h₂'
      exact h₃'
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by apply hNa;  apply le_max_left
  have absb : |s N - b| < ε := by apply hNb; apply le_max_right
  have : |a - b| < |a - b| :=
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by congr; ring
    _ ≤ |-(s N - a)| + |s N - b| := by apply abs_add
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := by apply add_lt_add absa absb
    _= |a - b| := by norm_num [ε]
  exact lt_irrefl |a - b| this

#check abs_of_pos
#check lt_or_gt_of_ne
#check pos_of_neg_neg
#check lt_of_lt_of_eq
#check le_of_max_le_left
#check add_lt_add
#check add_zero
#check sub_self
#check abs_add



section
variable {α : Type*} [LinearOrder α]

def ConvergesTo'' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
