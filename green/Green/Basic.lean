import Mathlib.Tactic

#allow_unused_tactic Lean.Parser.Tactic.done

namespace Green

example (p q : Prop) (hpq : p ∧ q) : q ∧ p := by
  -- exact id (And.symm hpq)
  ---- this lemma exists and `exact?` finds it for us
  constructor  -- splits the `and` in the goal into two separate goals
  · cases hpq  -- place the cursor at the end of `hpq`, wait for 💡 to appear and click on it!
    assumption
  · cases hpq
    assumption
  done

example (a b : Real) (hab : a < b) : Set.Icc b a = ∅ := by
    apply Set.Icc_eq_empty_of_lt
    assumption
    done

example (a b : Real) : ∫ _ in a..b, 1 = b - a  := by
    rewrite [<- mul_one (b - a)]
    apply intervalIntegral.integral_const
    done

example (a b : Real) : ∫ _ in a..b, 1 = b - a  := by
    apply intervalIntegral.integral_deriv_eq_sub'
    · exact deriv_id'
    · exact fun x a ↦ differentiableAt_id'
    · exact continuousOn_const
    done

example (a b c : Real) (h : c ≠ 0) : c*a = c*b → a = b := by
    apply mul_left_cancel₀
    apply h

example (a b : Real) : ∫ _ in a..b, 2 = 2*(b - a)  := by
    rewrite (occs := .pos [1]) [<- one_mul 2, intervalIntegral.integral_mul_const, mul_comm]
    rw [mul_left_cancel_iff_of_pos]
    apply intervalIntegral.integral_deriv_eq_sub'
    · apply deriv_eq
      intro x
      exact hasDerivAt_id' x
    · exact fun x a ↦ differentiableAt_id'
    · exact continuousOn_const
    apply zero_lt_two
    done

example (a b : Real) : ∫ _ in a..b, 2 = 2*(b - a)  := by
    rw [mul_sub_left_distrib]
    apply intervalIntegral.integral_deriv_eq_sub'
    · apply deriv_eq
      intro x -- idk how refine works, everything above has gone to great effort to avoid it (and simp since it just solves them) cuz it just breaks
      --refine HasDerivWithinAt.hasDerivAt ?hderiv.h.h ?hderiv.h.hs
      apply?
    · apply?
    · exact continuousOn_const
    done

variable [NormedSpace ℝ ℝ] -- can generalise second R to a normedaddcommgroup or something judging by the definitions
variable {a b : ℝ} {f g : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}


theorem FTC2 {f' : ℝ → ℝ} (dd : f' = deriv f): ∫ x in a..b, f' x = f b - f a := by
  sorry -- also don't think the statement is right
  done

theorem integral_neg_reverse (F : f = deriv g): ∫ x in a..b, f x = - ∫ x in b..a, f x := by
  rw [FTC2 F, FTC2 F]
  norm_num
  done

theorem integral_neg_reverse2 : ∫ x in a..b, f x = - ∫ x in b..a, f x := by
  unfold intervalIntegral
  --rw [FTC2 F, FTC2 F]
  norm_num
  done

theorem integral_same : ∫ x in a..a, f x = 0 := by
  unfold intervalIntegral
  apply sub_self _
  done

theorem integral_const_mul {c : ℝ} : ∫ x in a..b, c * (f x) ∂μ = c * (∫ x in a..b, f x ∂μ) := by
  simp only [intervalIntegral, MeasureTheory.integral_smul, smul_sub] -- this is docs method
  -- the doc version pipes all the way back to the abstracted integral definition to do this -- maybe if possible it could be easier to make our own definition of integral and work off that with normal, sensible maths
  sorry
  done

class Region (α : Type) where
  a : α
  b : α
  f_t : α → α
  f_b : α → α -- can't subscript a b??

structure Simple_region where
  a : ℝ
  b : ℝ
  f_t : ℝ → ℝ
  f_b : ℝ → ℝ -- can't make these a general thing even if i tell it the general thing is ℝ?
  no_cross : ∀ x, f_t x >= f_b x

theorem abba (c : ℝ): ∀ x, c = (fun (d : ℝ) ↦ c) x := by
  exact fun x ↦ rfl
  done

#check Simple_region.no_cross (Simple_region.mk 3 4 1 2 sorry)
example : (2 : ℝ) <= 1 := by
  rw [abba 2, abba 1]
  apply Simple_region.no_cross (Simple_region.mk 3 4 1 2 sorry)
  repeat assumption
  done

variable {L : ℝ×ℝ → ℝ}
variable {k : ℝ → ℝ×ℝ}

noncomputable
def pathIntegral (r : ℝ → ℝ×ℝ) (f : ℝ×ℝ → ℝ) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in (0)..(1), (fun x ↦ (f (r x)) * norm (deriv r x)) x ∂μ

notation3"∫ "(...)" in "a", "p:60:(scoped f => f)" ∂"μ:70 => pathIntegral a p μ

#check ∫ x in k, (fun l ↦ l.1 + l.2) x ∂μ
