import Mathlib.Tactic

#allow_unused_tactic Lean.Parser.Tactic.done

namespace Region

structure SimpleRegion where
  a : ℝ
  b : ℝ
  f_t : ℝ → ℝ
  f_b : ℝ → ℝ -- can't make these a general thing even if i tell it the general thing is ℝ?
  no_cross : ∀ x, f_t x >= f_b x

end Region

namespace PathIntegral

variable [NormedSpace ℝ ℝ] -- can generalise second R to a normedaddcommgroup or something judging by the definitions
variable {a b : ℝ} {f g : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}
variable {L : ℝ×ℝ → ℝ}
variable {k : ℝ → ℝ×ℝ}
variable {p1 p2 : ℝ×ℝ}

noncomputable
def pathIntegral (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in (0)..(1), (fun x ↦ (f (r x)) * norm (deriv r x)) x ∂μ

-- todo: update the notation syntax to lean 4, and also like get the second one to work idk
notation3"∫ "(...)" in "a", "p:60:(scoped f => f)" ∂"μ:70 => pathIntegral p a μ
notation3"∫ "(...)" in "a", "p:60:(scoped f => pathIntegral f a MeasureTheory.volume) => a

-- todo: coersion between version 1/2/3?
noncomputable
def pathIntegral2 (f : ℝ×ℝ → ℝ) (r : Path p1 p2) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in (0)..(1), (fun x ↦ (f (r.extend x)) * norm (deriv r.extend x)) x ∂μ

noncomputable
def pathIntegral3 (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in a..b, (fun x ↦ (f (r x)) * norm (deriv r x)) x ∂μ

noncomputable
def pathIntegral3_proj_fst (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in a..b, (fun x ↦ (f (r x)) * norm ((deriv r x).fst)) x ∂μ

-- It works!
variable [MeasureTheory.IsLocallyFiniteMeasure μ]

-- generalising? ?
def pathIntegral3Integrable (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : Prop :=
  IntervalIntegrable (fun x ↦ (f (r x)) * norm (deriv r x)) μ a b

def pathIntegral3_proj_fst_Integrable (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : Prop :=
  IntervalIntegrable (fun x ↦ (f (r x)) * norm ((deriv r x).fst)) μ a b


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

omit [MeasureTheory.IsLocallyFiniteMeasure μ]

theorem pathIntegral3_proj_fst_Integrable_trans {c : ℝ} (hac : pathIntegral3_proj_fst_Integrable a c L k μ) (hcb : pathIntegral3_proj_fst_Integrable c b L k μ) : pathIntegral3_proj_fst_Integrable a b L k μ := by
  unfold pathIntegral3_proj_fst_Integrable
  apply IntervalIntegrable.trans hac hcb
  done

-- more general? -- this is how the docs do it for normal intervalIntegrals afaict
theorem pathIntegral3_split_at2 (c : ℝ) {hac : pathIntegral3Integrable a c L k μ} {hcb : pathIntegral3Integrable c b L k μ} : pathIntegral3 a c L k μ + pathIntegral3 c b L k μ = pathIntegral3 a b L k μ := by
  unfold pathIntegral3
  apply intervalIntegral.integral_add_adjacent_intervals
  repeat assumption
  done

theorem pathIntegral3_proj_fst_split_at2 (c : ℝ) {hac : pathIntegral3_proj_fst_Integrable a c L k μ} {hcb : pathIntegral3_proj_fst_Integrable c b L k μ} : pathIntegral3_proj_fst a c L k μ + pathIntegral3_proj_fst c b L k μ = pathIntegral3_proj_fst a b L k μ := by
  unfold pathIntegral3_proj_fst
  apply intervalIntegral.integral_add_adjacent_intervals
  repeat assumption
  done

-- relies on lebesgue measure (μ = MeasureTheory.volume)
theorem pathIntegral3_equal_translate_exact : pathIntegral3 a b L k MeasureTheory.volume = pathIntegral3 0 (b-a) L (fun x ↦ k (x+a)) MeasureTheory.volume := by
  have haa : a - a = 0 := by
    simp
  unfold pathIntegral3
  simp_rw [<- haa, deriv_comp_add_const, <- intervalIntegral.integral_comp_sub_right _ a]
  simp
  done

theorem pathIntegral3_equal_translate_exact_arbitrary (c : ℝ): pathIntegral3 a b L k MeasureTheory.volume = pathIntegral3 (a + c) (b + c) L (fun x ↦ k (x-c)) MeasureTheory.volume := by
  unfold pathIntegral3
  simp_rw [deriv_comp_sub_const, <- intervalIntegral.integral_comp_add_right _ c]
  simp
  done

-- halp
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

end PathIntegral

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
theorem green_split_alpha (s_1 s_2 s_3 : ℝ) (hi0 : pathIntegral3_proj_fst_Integrable 0 s_1 L k MeasureTheory.volume) (hi1 : pathIntegral3_proj_fst_Integrable s_1 s_2 L k MeasureTheory.volume) (hi2 : pathIntegral3_proj_fst_Integrable s_2 s_3 L k MeasureTheory.volume) (hi3 : pathIntegral3_proj_fst_Integrable s_3 1 L k MeasureTheory.volume) (hs01 : pathIntegral3_proj_fst 0 s_1 L k MeasureTheory.volume = ∫ x in a..b, L (x,f x)) (hs12 : pathIntegral3_proj_fst s_1 s_2 L k MeasureTheory.volume = 0) (hs23 : pathIntegral3_proj_fst s_2 s_3 L k MeasureTheory.volume = ∫ x in b..a, L (x,g x)) (hs30 : pathIntegral3_proj_fst s_3 1 L k MeasureTheory.volume = 0): pathIntegral3_proj_fst 0 1 L k MeasureTheory.volume = (∫ x in a..b, L (x,f x)) - ∫ x in a..b, L (x,g x) := by
  have hi20 : pathIntegral3_proj_fst_Integrable s_2 1 L k MeasureTheory.volume := by
    apply pathIntegral3_proj_fst_Integrable_trans hi2 hi3
  have hi10 : pathIntegral3_proj_fst_Integrable s_1 1 L k MeasureTheory.volume := by
    apply pathIntegral3_proj_fst_Integrable_trans hi1 hi20
  rw [<- pathIntegral3_proj_fst_split_at2 s_1]
  nth_rw 2 [<- pathIntegral3_proj_fst_split_at2 s_2]
  nth_rw 3 [<- pathIntegral3_proj_fst_split_at2 s_3]
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
