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
      apply?
    · apply?
    · exact continuousOn_const
    done
