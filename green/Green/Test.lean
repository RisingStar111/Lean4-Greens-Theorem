import Mathlib.Tactic

open Classical

#allow_unused_tactic Lean.Parser.Tactic.done
namespace Test

variable {E F A : Type*} [NormedAddCommGroup E]
variable {f : Option ℝ → ℝ}
--variable {f : ℝ → E} {a b : ℝ}

structure Partition (a b : ℝ) : Type where
  (points : List ℝ)
  (nonempty : points ≠ [])
  (zth : points.head? = some a)
  (nth : points.reverse.head? = some b)
  (ordered : ∀ i j, i < j → points.get? i < points.get? j)

structure PartitionFamily (a b : ℝ) : Type where
(partitions : ℕ → Partition a b)  -- A sequence of partitions
(subintervals_tend_to_zero :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ (partition := partitions n),
    ∀ i j, j = i + 1 →
      match partition.points.get? i, partition.points.get? j with
      | some xi, some xj => |xj - xi| < ε
      | _, _ => false)
--is it better to define by max width or number of intervals?

def seq_limit (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_at (f : Option ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε


noncomputable def max (S : Set ℕ) : ℕ :=
  if h : ∃ m ∈ S, ∀ s ∈ S, s ≤ m then
    Classical.choose h else default

noncomputable def natFloor (n : ℝ) : ℕ :=
max {m | m ≤ n}


def is_lim (f : ℝ → ℝ) (x₀ h : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - h| < ε

noncomputable def lim (f : ℝ → ℝ) (l : ℝ) : Option ℝ :=
if h : ∃ M, is_lim f l M then
    some (Classical.choose h)
else
    none


def differentiable_at (f : ℝ → ℝ) (x : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ h, ∃ M : ℝ, |h| < δ → |(f (x + h) - f x) / h| < M

def differentiable (f : ℝ → ℝ) : Prop :=
∀ x, differentiable_at f x

noncomputable def deriv (f : ℝ → ℝ) (x : ℝ) : Option ℝ :=
lim (fun h : ℝ => (f (x + h) - f x) / h) 0

def area (f : Option ℝ → ℝ) (a b : ℝ) (part : Partition a b) : ℝ :=
∑ᶠ k ≤ (part.points.length-1), k = (f (part.points.get? ((part.points.length-1)-1)) * |part.points.get? (part.points.length-1) - part.points.get? ((part.points.length-1)-1)|)
--does it go from k=0 or k=1

noncomputable def interval_integral (f : Option ℝ → ℝ) (a b : ℝ) : Option ℝ :=
if ∀ x ∈ Set.Icc a b, continuous_at f x then
  ∃ P : PartitionFamily a b, lim (fun n : ℝ => area f a b (P.partitions (natFloor n))) Inf.inf
else
  none
