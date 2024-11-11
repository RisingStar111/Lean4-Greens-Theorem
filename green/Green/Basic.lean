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
