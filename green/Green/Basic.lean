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

structure SimpleRegion where
  a : ℝ
  b : ℝ
  f_t : ℝ → ℝ
  f_b : ℝ → ℝ -- can't make these a general thing even if i tell it the general thing is ℝ?
  no_cross : ∀ x, f_t x >= f_b x

theorem abba (c : ℝ): ∀ x, c = (fun (d : ℝ) ↦ c) x := by
  exact fun x ↦ rfl
  done

#check SimpleRegion.no_cross (SimpleRegion.mk 3 4 1 2 sorry)
example : (2 : ℝ) <= 1 := by
  rw [abba 2, abba 1]
  apply SimpleRegion.no_cross (SimpleRegion.mk 3 4 1 2 sorry)
  repeat assumption
  done

variable {L : ℝ×ℝ → ℝ}
variable {k : ℝ → ℝ×ℝ}

noncomputable
def pathIntegral (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in (0)..(1), (fun x ↦ (f (r x)) * norm (deriv r x)) x ∂μ

-- todo: update the notation syntax to lean 4, and also like get the second one to work idk
notation3"∫ "(...)" in "a", "p:60:(scoped f => f)" ∂"μ:70 => pathIntegral p a μ
notation3"∫ "(...)" in "a", "p:60:(scoped f => pathIntegral f a MeasureTheory.volume) => a

#check ∫ x in k, (fun l ↦ l.1 + l.2) x
#check ∫ x in k, (fun l ↦ l.1 + l.2) x ∂μ
#check ∫ x in k, L x ∂μ
#check ∫ x in (0)..(1), (fun l ↦ l) x

--variable [TopologicalSpace (ℝ×ℝ)]
variable {p1 p2 : ℝ×ℝ}

-- todo: coersion between version 1/2?
noncomputable
def pathIntegral2 (f : ℝ×ℝ → ℝ) (r : Path p1 p2) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in (0)..(1), (fun x ↦ (f (r.extend x)) * norm (deriv r.extend x)) x ∂μ

noncomputable
def pathIntegral3 (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in a..b, (fun x ↦ (f (r x)) * norm (deriv r x)) x ∂μ

-- theorem pathIntegral_split_at (c : ℝ) : ∫ x in k, L x ∂μ = ∫ x in (fun l ↦ k (1/c * l)), L x ∂μ + ∫ x in (fun l ↦ k (1/(1-c) * l + c)), L x ∂μ := by
--   unfold pathIntegral
--   simp

--   sorry
--   done

-- It works!
variable [MeasureTheory.IsLocallyFiniteMeasure μ]

-- generalising? ?
def pathIntegral3Integrable (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : Prop :=
  IntervalIntegrable (fun x ↦ (f (r x)) * norm (deriv r x)) μ a b

-- this is actually too strong a condition, just need norm(deriv) continuous - in particular this can't do corners atm
theorem continuous_pathIntegral3_intervalIntegrable {hl : Continuous L} {hk : Continuous k} {hdk : Continuous (deriv k)} : pathIntegral3Integrable a b L k μ := by
  unfold pathIntegral3Integrable
  refine Continuous.intervalIntegrable ?h a b
  apply Continuous.mul
  exact Continuous.comp' hl hk
  apply Continuous.norm
  exact hdk
  done

theorem norm_continuous_pathIntegral3_intervalIntegrable {hl : Continuous L} {hk : Continuous k} {hdk : Continuous (fun x ↦ ‖deriv k x‖)} : pathIntegral3Integrable a b L k μ := by
  unfold pathIntegral3Integrable
  refine Continuous.intervalIntegrable ?h a b
  apply Continuous.mul
  exact Continuous.comp' hl hk
  exact hdk
  done

-- original
theorem pathIntegral3_split_at (c : ℝ) {hl : Continuous L} {hk : Continuous k} {hdk : Continuous (deriv k)} : pathIntegral3 a c L k μ + pathIntegral3 c b L k μ = pathIntegral3 a b L k μ := by
  unfold pathIntegral3
  apply intervalIntegral.integral_add_adjacent_intervals
  · refine Continuous.intervalIntegrable ?h a c
    apply Continuous.mul
    exact Continuous.comp' hl hk
    apply Continuous.norm
    exact hdk
  · refine Continuous.intervalIntegrable ?h c b -- idk why this doesn't need the rest
  done

-- more general? -- this is how the docs do it for normal intervalIntegrals afaict
omit [MeasureTheory.IsLocallyFiniteMeasure μ] in -- compiler told me this is probably a good thing
theorem pathIntegral3_split_at2 (c : ℝ) {hac : pathIntegral3Integrable a c L k μ} {hcb : pathIntegral3Integrable c b L k μ} : pathIntegral3 a c L k μ + pathIntegral3 c b L k μ = pathIntegral3 a b L k μ := by
  unfold pathIntegral3
  apply intervalIntegral.integral_add_adjacent_intervals
  repeat assumption
  done

-- relies on lebesgue measure (μ = MeasureTheory.volume)
omit [MeasureTheory.IsLocallyFiniteMeasure μ] in
theorem pathIntegral3_equal_translate : ∃j, pathIntegral3 a b L k MeasureTheory.volume = pathIntegral3 0 (b-a) L j MeasureTheory.volume := by
  use fun w ↦ k (w+a)
  have haa : a - a = 0 := by
    simp
  unfold pathIntegral3
  simp_rw [<- haa, deriv_comp_add_const, <- intervalIntegral.integral_comp_sub_right _ a]
  simp
  done

omit [MeasureTheory.IsLocallyFiniteMeasure μ] in
theorem pathIntegral3_equal_translate_exact : pathIntegral3 a b L k MeasureTheory.volume = pathIntegral3 0 (b-a) L (fun x ↦ k (x+a)) MeasureTheory.volume := by
  have haa : a - a = 0 := by
    simp
  unfold pathIntegral3
  simp_rw [<- haa, deriv_comp_add_const, <- intervalIntegral.integral_comp_sub_right _ a]
  simp
  done

omit [MeasureTheory.IsLocallyFiniteMeasure μ] in
theorem pathIntegral3_equal_translate_exact_arbitrary (c : ℝ): pathIntegral3 a b L k MeasureTheory.volume = pathIntegral3 (a + c) (b + c) L (fun x ↦ k (x-c)) MeasureTheory.volume := by
  unfold pathIntegral3
  simp_rw [deriv_comp_sub_const, <- intervalIntegral.integral_comp_add_right _ c]
  simp
  done

-- oh that's a sneaky thing innit -- the path integral is *not* over dk, but dx - need a way to project the path integral
theorem green_split_alpha (s_1 s_2 s_3 : ℝ) (hs01 : pathIntegral3 0 s_1 L k MeasureTheory.volume = ∫ x in (0)..s_1, L (x,f x)) (hs12 : pathIntegral3 s_1 s_2 L k MeasureTheory.volume = ∫ x in s_1..s_2, L (x, 0)): pathIntegral3 0 1 L k MeasureTheory.volume = ∫ x in a..b, L (x,f x) - ∫ x in a..b, L (x,g x) := by

  sorry
  done

-- halp
omit [MeasureTheory.IsLocallyFiniteMeasure μ] in
-- set_option diagnostics true in
theorem pathIntegral3_equal_scale {vv : μ = MeasureTheory.volume} (c : ℝ) : ∃j, pathIntegral3 a b L k μ = pathIntegral3 (c*a) (c*b) L j μ := by
  use fun w ↦ k (w/c)
  unfold pathIntegral3
  -- have : (fun w ↦ k (c * w)) = k ∘ (HMul.hMul c) := by
  --   rfl
  have tt : ∀x, deriv (fun w ↦ k (w / c)) x = deriv k (x / c) / (c, c) := by
    sorry
    done
  conv => rhs; pattern ‖_‖; congr; rw [tt] -- ^ ^!!
  rw [vv, <- intervalIntegral.smul_integral_comp_mul_left _ c]
  simp
  have : c ≠ 0 := by sorry
  conv => rhs; pattern _ * _; rw [mul_comm c, mul_div_assoc, div_self]; rfl; exact this
  simp
  have : ∀x, ‖deriv k x / (c,c)‖ = ‖k x‖ / |c| := by
    intro x
    -- apply?
    sorry
    done
  simp_rw [this]
  simp_rw [div_eq_inv_mul]
  conv => rhs; pattern _ * _; rw [<- mul_assoc]; rw [mul_comm (L _), mul_assoc]
  conv => rhs; rw [<- intervalIntegral.integral_smul]
  have : c > 0 := by
    sorry
  rw [abs_of_pos]
  conv => rhs; pattern _ • _; rw [<- smul_mul_assoc]

  done
