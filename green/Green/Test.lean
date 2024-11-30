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


def differentiable_at (f : ℝ → ℝ) (x : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ h, ∃ M : ℝ, |h| < δ → |(f (x + h) - f x) / h| < M

def differentiable (f : ℝ → ℝ) : Prop :=
∀ x, differentiable_at f x

noncomputable def deriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
lim (fun h : ℝ => (f (x + h) - f x) / h) 0


noncomputable def area (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
∑ k in Set.Icc 0 (n-1), (f (a + ↑k * (a - b) / ↑n) * 1/↑n)

noncomputable def interval_integral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
if (∀ x : Set.Icc a b, |f x| < inf) ∧ (∀ x : Set.Icc a b, continuous_at f x) then
  lim (fun n : ℝ => area f a b (natFloor n)) inf
else
  default

theorem int_c_eq_c_int {f g : ℝ → ℝ} (c : ℝ) (h: ∀ x ∈ Set.Icc a b, g x = c * f x)  : interval_integral g a b = c * interval_integral f a b :=
sorry
