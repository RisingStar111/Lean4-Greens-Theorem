import Mathlib.Tactic

#allow_unused_tactic Lean.Parser.Tactic.done

-- Currently unused but aiming to be used but skill issue/potentially useful/references
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

theorem Ioo_inter_Ici_of_ge {a b c : ℝ} (h : a ≤ c): Set.Ioo a b ∩ Set.Ici c = Set.Ico c b := by
  -- simp only [Set.inter_eq_left]
  rw [Set.Ioo, Set.Ici, Set.Ico, Set.inter_def]
  simp
  simp_rw [and_comm (a := a < _), and_assoc]
  let x : ℝ
  sorry
  have aaa : a < x ∧ c ≤ x → c ≤ x := by
    simp only [and_imp, imp_self, implies_true]

  apply aaa
  aesop -- needs to be le not just lt so can't use the iff in the middle

  done

theorem Ioo_inter_Ici {a b c : ℝ} : Set.Ioo a b ∩ Set.Ici c ⊆ Set.Ici (max a c) := by
  suffices : Set.Ici a ∩ Set.Ici c ⊆ Set.Ici (a ⊔ c)
  suffices : Set.Ioi a ∩ Set.Ici c ⊆ Set.Ici (a ⊔ c)
  simp_rw [Set.Ioo, Set.Ici]
  simp
  refine Set.subset_setOf.mpr ?this.a
  intro x a_1
  simp_all only [Set.Ici_inter_Ici, subset_refl, Set.mem_inter_iff, Set.mem_setOf_eq, and_true]
  obtain ⟨left, right⟩ := a_1
  apply le_of_lt
  exact left.left

  simp_rw [Set.Ioi, Set.Ici]
  simp
  refine Set.subset_setOf.mpr ?this.b
  intro x a_1
  simp_all only [Set.Ici_inter_Ici, subset_refl, Set.mem_inter_iff, Set.mem_setOf_eq, and_true]
  obtain ⟨left, right⟩ := a_1
  apply le_of_lt
  exact left

  simp only [Set.Ici_inter_Ici, subset_refl]
  done -- yikes

theorem pathIntegral_proj_fst_Integrable_translate_zero (hi : pathIntegral_proj_fst_Integrable a b L k MeasureTheory.volume) : pathIntegral_proj_fst_Integrable 0 (b-a) L (fun x ↦ k (x+a)) MeasureTheory.volume := by
  have haa : a - a = 0 := by
    simp
  unfold pathIntegral_proj_fst_Integrable
  simp_rw [<- haa, deriv_comp_add_const]
  have : (fun x ↦ L (k (x + a)) * (deriv k (x + a)).1) = fun x ↦ ((fun x ↦ L (k (x)) * (deriv k (x)).1) (x + a)) := by
    rfl
  rw [this]
  apply IntervalIntegrable.comp_add_right (f := (fun x ↦ L (k (x)) * (deriv k (x)).1))-- not sure what complicated this so much
  exact hi
  done

theorem Ioo_inter_Ici_of_le {a b c : ℝ} (h : c ≤ a): Set.Ioo a b ∩ Set.Ici c = Set.Ioo a b := by
  simp only [Set.inter_eq_left]
  rw [Set.Ioo, Set.Ici]
  simp_all only [Set.setOf_subset_setOf, and_imp]
  intro a_1 a_2 a_3
  apply le_of_lt
  exact lt_of_le_of_lt h a_2
  done

theorem deriv_piecewise_Ioo_of_lt [NoAtoms μ] (hab : a < b) : deriv ((Set.Ioo a b).piecewise f g) =ᵐ[μ] (Set.Ioo a b).piecewise (deriv f) (deriv g) := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  use (Set.Ioo a b) ∪ (Set.Iio a) ∪ (Set.Ioi b)
  simp_all only [Set.eqOn_union]
  apply And.intro
  · rw [mem_ae_iff]
    have : (Set.Ioo a b ∪ Set.Iio a ∪ Set.Ioi b)ᶜ = {x | x = a ∨ x = b} := by
      simp only [Set.compl_union, Set.compl_Iio, Set.compl_Ioi]
      rw [Set.inter_assoc]
      rw [Set.Ici_inter_Iic]
      rw [Set.Ioo, Set.Icc]
      rw [Set.compl_def]
      simp only [Set.mem_setOf_eq, not_lt]
      have adddee : ∀ x, ¬(a < x ∧ x < b) ↔ (a < x ↔ ¬(x < b)) := by
        intro x
        simp_all only [not_and, not_lt]
        apply Iff.intro
        · intro a_1
          apply Iff.intro
          · intro a_2
            simp_all only [forall_const]
          · intro a_2
            simp_all only [implies_true]
            apply lt_of_lt_of_le hab a_2
        · intro a_1 a_2
          simp_all only [true_iff]

      simp_rw [adddee]
      rw [Set.inter_def]
      simp
      apply Set.ext
      intro x
      by_cases aaaaa: a < x
      aesop
      apply Or.intro_right
      apply eq_of_le_of_le right left
      apply le_of_lt hab

      simp
      rw [not_lt] at aaaaa

      aesop
      apply Or.intro_left
      apply eq_of_le_of_le aaaaa left_1
      apply le_of_lt hab
      apply le_of_lt hab

    rw [this]
    suffices : {x | x = a ∨ x = b} = {a, b}
    rw [this]
    apply Set.Finite.measure_zero
    exact Set.toFinite {a, b}
    simp_all only [Set.compl_union, Set.compl_Iio, Set.compl_Ioi]
    rfl

  aesop
  intro x a_1
  have : derivWithin ((Set.Ioo a b).piecewise f g) (Set.Ioo a b) x = deriv ((Set.Ioo a b).piecewise f g) x := by
    apply derivWithin_of_mem_nhds
    apply mem_interior_iff_mem_nhds.mp
    simp_all only [Set.mem_Ioo, interior_Ioo, and_self]
  rw [<- this]
  rw [derivWithin_congr (f := f)]
  simp_all only [Set.piecewise_eq_of_mem]
  have : derivWithin f (Set.Ioo a b) x = deriv f x := by
    apply derivWithin_of_mem_nhds
    apply mem_interior_iff_mem_nhds.mp
    simp_all only [Set.mem_Ioo, interior_Ioo, and_self]
  exact this
  exact Set.piecewise_eqOn (Set.Ioo a b) f g
  exact Set.piecewise_eq_of_mem (Set.Ioo a b) f g a_1

  intro x a_1
  have : derivWithin ((Set.Ioo a b).piecewise f g) (Set.Iio a) x = deriv ((Set.Ioo a b).piecewise f g) x := by
    apply derivWithin_of_mem_nhds
    apply mem_interior_iff_mem_nhds.mp
    simp_all only [Set.mem_Iio, interior_Iio]
  rw [<- this]
  have fofo : x ∈ (Set.Ioo a b)ᶜ := by
    aesop
    apply lt_trans a_1 at a_2
    rw [lt_self_iff_false] at a_2
    exact False.elim a_2
  rw [derivWithin_congr (f := g)]
  have asi : (Set.Ioo a b).piecewise (deriv f) (deriv g) x = deriv g x := by
    rw [<- Set.piecewise_compl]
    simp_all only [Set.mem_Iio, Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt, implies_true, Set.piecewise_eq_of_mem]
  rw [asi]
  have : derivWithin g (Set.Iio a) x = deriv g x := by
    apply derivWithin_of_mem_nhds
    apply mem_interior_iff_mem_nhds.mp
    simp_all only [Set.mem_Iio, interior_Iio]
  exact this
  rw [Set.eqOn_piecewise]
  aesop
  rw [Set.Iio_inter_Ioo]
  aesop
  apply Set.eqOn_refl
  exact Set.piecewise_eq_of_not_mem (Set.Ioo a b) f g fofo

  intro x a_1
  have : derivWithin ((Set.Ioo a b).piecewise f g) (Set.Ioi b) x = deriv ((Set.Ioo a b).piecewise f g) x := by
    apply derivWithin_of_mem_nhds
    apply mem_interior_iff_mem_nhds.mp
    simp_all only [Set.mem_Ioi, interior_Ioi]
  rw [<- this]
  have fofo : x ∈ (Set.Ioo a b)ᶜ := by
    aesop
    apply le_of_lt
    exact a_1
  rw [derivWithin_congr (f := g)]
  have asi : (Set.Ioo a b).piecewise (deriv f) (deriv g) x = deriv g x := by
    rw [<- Set.piecewise_compl]
    simp_all only [Set.mem_Iio, Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt, implies_true, Set.piecewise_eq_of_mem]
  rw [asi]
  have : derivWithin g (Set.Ioi b) x = deriv g x := by
    apply derivWithin_of_mem_nhds
    apply mem_interior_iff_mem_nhds.mp
    simp_all only [Set.mem_Ioi, interior_Ioi]
  exact this
  rw [Set.eqOn_piecewise]
  aesop
  rw [Set.Ioi_inter_Ioo]
  aesop
  apply Set.eqOn_refl
  exact Set.piecewise_eq_of_not_mem (Set.Ioo a b) f g fofo
  done
