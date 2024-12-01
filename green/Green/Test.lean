import Mathlib.Tactic

open Classical

#allow_unused_tactic Lean.Parser.Tactic.done
namespace Test


variable {f : ℝ → ℝ} {a b : ℝ}


def seq_limit (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

noncomputable def max (S : Set ℝ) : ℝ :=
  if h : ∃ m ∈ S, ∀ s ∈ S, s ≤ m then
    Classical.choose h else default

noncomputable def maxNat (S : Set ℕ) : ℕ :=
  if h : ∃ m ∈ S, ∀ s ∈ S, s ≤ m then
    Classical.choose h else default

noncomputable def natFloor (n : ℝ) : ℕ :=
maxNat {m | m ≤ n}


noncomputable def inf : ℝ := max {r | r > 0}

def is_lim (f : ℝ → ℝ) (x₀ h : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - h| < ε

noncomputable def lim (f : ℝ → ℝ) (l : ℝ) : ℝ :=
if ∃ M, is_lim f l M then
    f l
else
    default

theorem lim_const_eq_const {f : ℝ → ℝ} (l : ℝ) (c : ℝ) (h : ∀ x : ℝ, f x = c) : lim f l = c := by {
  unfold lim
  split_ifs with hlim
  apply h

  exfalso
  apply hlim
  use c
  unfold is_lim
  intro ε ε_pos
  use 1
  simp
  intro x hδ
  rw [h]
  simp
  exact ε_pos
  done
}


def differentiable_at (f : ℝ → ℝ) (x : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ h, ∃ M : ℝ, |h| < δ → |(f (x + h) - f x) / h| < M

def differentiable (f : ℝ → ℝ) : Prop :=
∀ x, differentiable_at f x

noncomputable def deriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
lim (fun h : ℝ => (f (x + h) - f x) / h) 0


noncomputable def area (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
∑ k in Set.Icc 0 (n-1), (f (a + ↑k * (b - a) / ↑n) * (b - a) / ↑n)

noncomputable def interval_integral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
if ∀ x : Set.Icc a b, continuous_at f x then
  lim (fun n : ℝ => area f a b (natFloor n)) inf
else
  default

theorem int_aa_eq_zero {f : ℝ → ℝ} : interval_integral f a a = 0 := by {
unfold interval_integral
simp
split
unfold area
simp
apply lim_const_eq_const
simp
rfl
done
}

theorem int_c_eq_c_int {f g : ℝ → ℝ} (c : ℝ) (h: ∀ x ∈ Set.Icc a b, g x = c * f x)  : interval_integral g a b = c * interval_integral f a b := by {
unfold interval_integral
split




}
