import Mathlib.Tactic

#allow_unused_tactic Lean.Parser.Tactic.done

-- Currently unused but potentially useful/references
namespace Deprecated

namespace PathIntegral

variable [NormedSpace ℝ ℝ] -- can generalise second R to a normedaddcommgroup or something judging by the definitions
variable {a b : ℝ} {f g : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}
variable {L : ℝ×ℝ → ℝ}
variable {k : ℝ → ℝ×ℝ}
variable {p1 p2 : ℝ×ℝ}

noncomputable
def pathIntegral2 (f : ℝ×ℝ → ℝ) (r : Path p1 p2) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in (0)..(1), (fun x ↦ (f (r.extend x)) * norm (deriv r.extend x)) x ∂μ

noncomputable
def pathIntegral3 (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ x in a..b, (fun x ↦ (f (r x)) * norm (deriv r x)) x ∂μ

def pathIntegral3Integrable (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : MeasureTheory.Measure ℝ) : Prop :=
  IntervalIntegrable (fun x ↦ (f (r x)) * norm (deriv r x)) μ a b

theorem norm_continuous_pathIntegral3_intervalIntegrable [MeasureTheory.IsLocallyFiniteMeasure μ] {hl : Continuous L} {hk : Continuous k} {hdk : Continuous (fun x ↦ ‖deriv k x‖)} : pathIntegral3Integrable a b L k μ := by
  unfold pathIntegral3Integrable
  refine Continuous.intervalIntegrable ?h a b
  apply Continuous.mul
  exact Continuous.comp' hl hk
  exact hdk
  done

theorem pathIntegral3_split_at2 (c : ℝ) {hac : pathIntegral3Integrable a c L k μ} {hcb : pathIntegral3Integrable c b L k μ} : pathIntegral3 a c L k μ + pathIntegral3 c b L k μ = pathIntegral3 a b L k μ := by
  unfold pathIntegral3
  apply intervalIntegral.integral_add_adjacent_intervals
  repeat assumption
  done

-- relies on lebesgue measure (μ = MeasureTheory.volume)
theorem pathIntegral3_equal_translate : pathIntegral3 a b L k MeasureTheory.volume = pathIntegral3 0 (b-a) L (fun x ↦ k (x+a)) MeasureTheory.volume := by
  have haa : a - a = 0 := by
    simp
  unfold pathIntegral3
  simp_rw [<- haa, deriv_comp_add_const, <- intervalIntegral.integral_comp_sub_right _ a]
  simp
  done

theorem pathIntegral3_equal_translate_arbitrary (c : ℝ): pathIntegral3 a b L k MeasureTheory.volume = pathIntegral3 (a + c) (b + c) L (fun x ↦ k (x-c)) MeasureTheory.volume := by
  unfold pathIntegral3
  simp_rw [deriv_comp_sub_const, <- intervalIntegral.integral_comp_add_right _ c]
  simp
  done

-- halp
-- apply transform to coord, then throw it in function is different to throw in transformed function cuz of taking deriv? - yes. real maths we need to transform the function here - the deriv is *at the point* not *of the function applied to x*
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
