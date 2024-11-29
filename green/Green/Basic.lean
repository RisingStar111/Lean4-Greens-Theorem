import Mathlib.Tactic

#allow_unused_tactic Lean.Parser.Tactic.done

namespace PathIntegral

open MeasureTheory

variable [NormedSpace ℝ ℝ] -- can generalise second R to a normedaddcommgroup or something judging by the definitions
variable {a b : ℝ} {f g : ℝ → ℝ} {μ : Measure ℝ}
variable {L : ℝ×ℝ → ℝ}
variable {k : ℝ → ℝ×ℝ}
variable {p1 p2 : ℝ×ℝ}

-- todo: update the notation syntax to lean 4, and also like get the second one to work idk
-- notation3"∫ "(...)" in "a", "p:60:(scoped f => f)" ∂"μ:70 => pathIntegral p a μ
-- notation3"∫ "(...)" in "a", "p:60:(scoped f => pathIntegral f a volume) => a

noncomputable
def pathIntegral_proj_fst (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : Measure ℝ := volume) : ℝ :=
  ∫ x in a..b, (fun x ↦ (f (r x)) * norm ((deriv r x).fst)) x ∂μ

variable [IsLocallyFiniteMeasure μ] -- not sure why this behaves differently to putting it in the assumptions wrt the thms after it's ommitted

def pathIntegral3_proj_fst_Integrable (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : Measure ℝ := volume) : Prop :=
  IntervalIntegrable (fun x ↦ (f (r x)) * norm ((deriv r x).fst)) μ a b

omit [IsLocallyFiniteMeasure μ]

theorem pathIntegral_proj_fst_Integrable_trans {c : ℝ} (hac : pathIntegral3_proj_fst_Integrable a c L k μ) (hcb : pathIntegral3_proj_fst_Integrable c b L k μ) : pathIntegral3_proj_fst_Integrable a b L k μ := by
  unfold pathIntegral3_proj_fst_Integrable
  apply IntervalIntegrable.trans hac hcb
  done

theorem pathIntegral_proj_fst_split_at (c : ℝ) {hac : pathIntegral3_proj_fst_Integrable a c L k μ} {hcb : pathIntegral3_proj_fst_Integrable c b L k μ} : pathIntegral_proj_fst a c L k μ + pathIntegral_proj_fst c b L k μ = pathIntegral_proj_fst a b L k μ := by
  unfold pathIntegral_proj_fst
  apply intervalIntegral.integral_add_adjacent_intervals
  repeat assumption
  done

end PathIntegral

structure Region (a b : ℝ) (f g : ℝ → ℝ) where
  a : ℝ
  b : ℝ
  f_t : ℝ → ℝ
  f_b : ℝ → ℝ -- can't make these a general thing even if i tell it the general thing is ℝ?

namespace Region

open PathIntegral

variable {a b : ℝ} {f g : ℝ → ℝ}

structure SimpleRegion (a b : ℝ) (f g : ℝ → ℝ) extends Region a b f g where
  no_cross : ∀ x, f_b x <= f_t x
  positive_oriented : a <= b

variable (R : SimpleRegion a b f g)

noncomputable
def simple_boundary_function : ℝ → ℝ×ℝ :=
  fun r ↦ (
    if r < b then
      (r, R.f_b r)
    else if r < b+1 then
      (b, (R.f_b b) + (r - b) * (R.f_t b - R.f_b b))
    else if r < b+b+1-a then
      (b+b+1 - r, R.f_t (b+b+1 - r))
    else
      (a, (R.f_t a) - (r-(b+b+1-a)))
  )

end Region

namespace Green

open PathIntegral

-- variable [NormedSpace ℝ ℝ] -- can generalise second R to a normedaddcommgroup or something judging by the definitions
variable {a b : ℝ} {f g : ℝ → ℝ} --{μ : MeasureTheory.Measure ℝ}
variable {L : ℝ×ℝ → ℝ}
variable {k : ℝ → ℝ×ℝ}
-- variable {p1 p2 : ℝ×ℝ}

-- oh that's a sneaky thing innit -- the path integral is *not* over dk, but dx - need a way to project the path integral
-- easiest way out i think is to cast the deriv but that would need a new set of things
-- other option is to cast the path parametrisation but idk how that works with deriv - actually doesn't work because that's sent to the function as well
-- basically need to give the deriv some indication of what it's wrt ~~sneaky physicists~~
-- the projected norm not being continuous at the corners causes issues as to split the parts have to be integrable, but atm can only split one at a time meaning the rest has to be integrable in whole
theorem green_split_alpha (s_1 s_2 s_3 : ℝ) (hi0 : pathIntegral3_proj_fst_Integrable 0 s_1 L k) (hi1 : pathIntegral3_proj_fst_Integrable s_1 s_2 L k) (hi2 : pathIntegral3_proj_fst_Integrable s_2 s_3 L k) (hi3 : pathIntegral3_proj_fst_Integrable s_3 1 L k) (hs01 : pathIntegral_proj_fst 0 s_1 L k = ∫ x in a..b, L (x,f x)) (hs12 : pathIntegral_proj_fst s_1 s_2 L k = 0) (hs23 : pathIntegral_proj_fst s_2 s_3 L k = ∫ x in b..a, L (x,g x)) (hs30 : pathIntegral_proj_fst s_3 1 L k = 0): pathIntegral_proj_fst 0 1 L k = (∫ x in a..b, L (x,f x)) - ∫ x in a..b, L (x,g x) := by
  have hi20 : pathIntegral3_proj_fst_Integrable s_2 1 L k := by
    apply pathIntegral_proj_fst_Integrable_trans hi2 hi3
  have hi10 : pathIntegral3_proj_fst_Integrable s_1 1 L k := by
    apply pathIntegral_proj_fst_Integrable_trans hi1 hi20
  rw [<- pathIntegral_proj_fst_split_at s_1]
  nth_rw 2 [<- pathIntegral_proj_fst_split_at s_2]
  nth_rw 3 [<- pathIntegral_proj_fst_split_at s_3]
  all_goals first|assumption|skip
  rw [hs01, hs12, hs23, hs30, intervalIntegral.integral_symm a b]
  simp
  rfl
  done

theorem rhs_sub (hlcd : ∀x, Continuous (deriv fun w ↦ L (x, w))) (hlc : Continuous L) (hfc : Continuous f) (hgc : Continuous g) (hdf : ∀x, Differentiable ℝ (fun w ↦ L (x,w))) : ∫ x in a..b, (∫ y in (g x)..(f x), (-(deriv (fun w ↦ L (x,w)))) y) = (∫ x in a..b, L (x,g x)) - ∫ x in a..b, L (x,f x) := by
  simp
  have ftc : ∀x, ∫ (x_1 : ℝ) in g x..f x, deriv (fun w ↦ L (x, w)) x_1 = L (x, f x) - L (x, g x) := by
    intro x
    rw [intervalIntegral.integral_deriv_eq_sub]
    intro x_1 h
    apply hdf
    apply Continuous.intervalIntegrable
    apply hlcd
  simp_rw [ftc]
  rw [intervalIntegral.integral_sub]
  simp
  all_goals {
    apply Continuous.intervalIntegrable
    apply Continuous.comp
    assumption
    simp
    apply And.intro
    exact continuous_id
    assumption
  }
  done
