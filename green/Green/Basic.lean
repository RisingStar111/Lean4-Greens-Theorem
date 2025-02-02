import Mathlib.Tactic

#allow_unused_tactic Lean.Parser.Tactic.done

namespace PathIntegral

open MeasureTheory

variable [NormedSpace ℝ ℝ] -- can generalise second R to a normedaddcommgroup or something judging by the definitions
variable {a b : ℝ} {f g : ℝ → ℝ} {μ : Measure ℝ}
variable {L : ℝ×ℝ → ℝ}
variable {k : ℝ → ℝ×ℝ}

-- todo: update the notation syntax to lean 4, and also like get the second one to work idk
-- notation3"∫ "(...)" in "a", "p:60:(scoped f => f)" ∂"μ:70 => pathIntegral p a μ
-- notation3"∫ "(...)" in "a", "p:60:(scoped f => pathIntegral f a volume) => a

noncomputable
def pathIntegral_proj_fst (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : Measure ℝ := volume) : ℝ :=
  ∫ x in a..b, (fun x ↦ (f (r x)) * (deriv r x).fst) x ∂μ

variable [IsLocallyFiniteMeasure μ] -- not sure why this behaves differently to putting it in the assumptions wrt the thms after it's ommitted

def pathIntegral_proj_fst_Integrable (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : Measure ℝ := volume) : Prop :=
  IntervalIntegrable (fun x ↦ (f (r x)) * (deriv r x).fst) μ a b

theorem norm_continuous_pathIntegral_proj_fst_intervalIntegrable {hl : Continuous L} {hk : Continuous k} {hdk : Continuous (fun x ↦ (deriv k x).fst)} : pathIntegral_proj_fst_Integrable a b L k μ := by
  refine Continuous.intervalIntegrable ?h a b
  continuity
  done

theorem congr_ae_norm_continuous_pathIntegral_proj_fst_intervalIntegrable_Ioo [NoAtoms μ] {hab : a ≤ b} {hl : Continuous L} {hk : Continuous k} (o : ℝ → ℝ×ℝ) (hdo : Continuous (fun x ↦ (deriv o x).fst)) (hst : Set.EqOn (fun x ↦ (deriv k x).fst) (fun x ↦ (deriv o x).fst) (Set.Ioo a b)) : pathIntegral_proj_fst_Integrable a b L k μ := by
  unfold pathIntegral_proj_fst_Integrable
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]

  suffices IntegrableOn (fun x ↦ L (k x) * (deriv o x).1) (Set.Ioo a b) μ by
    apply IntegrableOn.congr_fun this
    exact fun ⦃x⦄ a_1 ↦ congrArg (HMul.hMul (L (k x))) (id (Set.EqOn.symm hst) a_1) -- apply? moment
    exact measurableSet_Ioo

  rw [<- integrableOn_Icc_iff_integrableOn_Ioo]
  apply Continuous.integrableOn_Icc
  apply Continuous.mul
  continuity
  assumption
  done

omit [IsLocallyFiniteMeasure μ]

theorem pathIntegral_proj_fst_Integrable_trans {c : ℝ} (hac : pathIntegral_proj_fst_Integrable a c L k μ) (hcb : pathIntegral_proj_fst_Integrable c b L k μ) : pathIntegral_proj_fst_Integrable a b L k μ := by
  unfold pathIntegral_proj_fst_Integrable
  apply IntervalIntegrable.trans hac hcb
  done

theorem pathIntegral_proj_fst_Integrable_on_union_reverse (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (hi : pathIntegral_proj_fst_Integrable a b L k μ) : pathIntegral_proj_fst_Integrable a c L k μ ∧ pathIntegral_proj_fst_Integrable c b L k μ := by
  unfold pathIntegral_proj_fst_Integrable at *
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le] at *
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le] -- ? why is this needed twice (neither simp_rw nor occs work)
  rw [<- Set.Ioc_union_Ioc_eq_Ioc (b := c), MeasureTheory.integrableOn_union] at hi
  exact hi
  exact hac
  exact hcb
  exact hcb
  exact Preorder.le_trans a c b hac hcb
  exact hac
  done

theorem pathIntegral_proj_fst_Integrable_on_union_left_reverse (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (hi : pathIntegral_proj_fst_Integrable a b L k μ) : pathIntegral_proj_fst_Integrable a c L k μ := by
  apply pathIntegral_proj_fst_Integrable_on_union_reverse c hac hcb at hi
  simp_all -- aesop moment? idk but also i couldn't work it out manually
  done

theorem pathIntegral_proj_fst_Integrable_on_union_right_reverse (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (hi : pathIntegral_proj_fst_Integrable a b L k μ) : pathIntegral_proj_fst_Integrable c b L k μ := by
  apply pathIntegral_proj_fst_Integrable_on_union_reverse c hac hcb at hi
  simp_all -- same ofc
  done

theorem pathIntegral_proj_fst_split_at (c : ℝ) {hac : pathIntegral_proj_fst_Integrable a c L k μ} {hcb : pathIntegral_proj_fst_Integrable c b L k μ} : pathIntegral_proj_fst a c L k μ + pathIntegral_proj_fst c b L k μ = pathIntegral_proj_fst a b L k μ := by
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

structure SimpleRegion (a b : ℝ) (f g : ℝ → ℝ) extends Region a b f g where
  no_cross : ∀ x, f_b x <= f_t x
  a_lt_b : a < b
  b_contDiff : ContDiff ℝ 1 f_b
  t_contDiff : ContDiff ℝ 1 f_t

variable {a b : ℝ} {f g : ℝ → ℝ}
variable {L : ℝ×ℝ → ℝ}
variable (R : SimpleRegion a b f g)

-- todo: version for arclength (|deriv| = 1) version and proof that |deriv| = 1, for use in integrability (or otherwise work out easier integrability)
noncomputable
def simple_boundary_function : ℝ → ℝ×ℝ :=
  Set.piecewise (Set.Iic R.b) (fun r ↦ (r, R.f_b r))
    (Set.piecewise (Set.Iic (R.b+1)) (fun r ↦ (R.b, (R.f_b R.b) + (r - R.b) * (R.f_t R.b - R.f_b R.b)))
      (Set.piecewise (Set.Iic (R.b+1+R.b-R.a)) (fun r ↦ (R.b+1+R.b - r, R.f_t (R.b+1+R.b - r)))
        (fun r ↦ (R.a, (R.f_t R.a) - (r-(R.b+1+R.b-R.a)) * (R.f_t R.a - R.f_b R.a)))))

theorem simple_boundary_continuous (hct : Continuous R.f_t) (hcb : Continuous R.f_b) : Continuous (simple_boundary_function R) := by
  unfold simple_boundary_function
  apply Continuous.piecewise
  simp
  continuity

  apply Continuous.piecewise
  simp_rw [Set.piecewise.eq_1]
  simp
  simp_rw [add_sub_assoc, le_add_iff_nonneg_right, sub_nonneg, le_of_lt R.a_lt_b, reduceIte]

  continuity -- yes i did this manually before gpt told me about this

  apply Continuous.piecewise
  simp -- originally was trying to do this manually before finding out that i'd changed the def badly, credit to lean for finding that out
  all_goals continuity -- since this is aesop it could also do the simps above it, but have left them separate to keep purpose clearer
  done

open PathIntegral

theorem boundary_part_integrable {a b : ℝ} {f g : ℝ → ℝ} {L : ℝ × ℝ → ℝ} (R : SimpleRegion a b f g) (hct : Continuous R.f_t)
  (f : ℝ → ℝ×ℝ)
  (hcb : Continuous R.f_b) {hl : Continuous L} {hrb : Continuous (deriv f)}
  {hrb2 : Differentiable ℝ f} (left right : ℝ) (hlr : left < right) (hse : Set.EqOn (simple_boundary_function R) f (Set.Ioo left right)):
  pathIntegral_proj_fst_Integrable left right L (simple_boundary_function R) := by

  have hr : Continuous (simple_boundary_function R) := by
    apply simple_boundary_continuous R hct hcb
  apply congr_ae_norm_continuous_pathIntegral_proj_fst_intervalIntegrable_Ioo
  apply le_of_lt
  apply hlr
  exact hl
  exact hr
  pick_goal 3
  use f
  continuity
  apply Set.EqOn.comp_left

  suffices : Set.EqOn (simple_boundary_function R) f (Set.Ioo left right)
  ·
    apply deriv_eqOn -- sure, need to be on open set, but this still doesn't help me actually get the range into the boundary
    exact isOpen_Ioo
    have hhhhh : ∀ x ∈ Set.Ioo left right, (simple_boundary_function R) x = f x:= by
      intro x a_1
      apply this
      simp_all only [Set.mem_Ioo, and_self] -- aesop simplified

    intro x hx
    refine HasDerivWithinAt.congr_of_mem ?kk this hx
    rw [<- derivWithin_of_isOpen, hasDerivWithinAt_derivWithin_iff,]
    apply DifferentiableAt.differentiableWithinAt
    apply Differentiable.differentiableAt
    have ldld : (ContDiff ℝ 1 f) := by
      rw [contDiff_one_iff_deriv]
      apply And.intro
      exact hrb2
      exact hrb
    apply ContDiff.differentiable ldld
    exact Preorder.le_refl 1
    exact isOpen_Ioo
    exact hx
  apply hse
  done

-- here partly due to an attempt to make simp work with them, but it just didn't idk
theorem contDiff_const_add (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 1 f) :
  ContDiff ℝ 1 (fun x ↦ c + f x) := ContDiff.add contDiff_const hf
theorem contDiff_add_const (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 1 f) :
  ContDiff ℝ 1 (fun x ↦ f x + c) := ContDiff.add hf contDiff_const

theorem contDiff_const_mul (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 1 f) :
  ContDiff ℝ 1 (fun x ↦ f x * c) := ContDiff.mul hf contDiff_const

theorem contDiff_const_sub (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 1 f) :
  ContDiff ℝ 1 (fun x ↦ c - f x) := ContDiff.sub contDiff_const hf
theorem contDiff_sub_const (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 1 f) :
  ContDiff ℝ 1 (fun x ↦ f x - c) := ContDiff.sub hf contDiff_const

theorem Ioo_inter_Iio_compl_self_right_eq_null (a b : ℝ) : Set.Ioo a b ∩ (Set.Iic b)ᶜ = ∅ := by
  rw [Set.compl_Iic, Set.Ioo_inter_Ioi]
  simp
theorem Ioo_inter_Iic_self_left_eq_null (a b : ℝ) : Set.Ioo a b ∩ Set.Iic a = ∅ := by
  -- aesop
  ext x : 1
  simp_all only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_and, not_le,
    implies_true]
theorem Ioo_inter_Iic_le_left_eq_null (a b c : ℝ) (h : c ≤ a) : Set.Ioo a b ∩ Set.Iic c = ∅ := by
  ext x : 1
  simp_all only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_and, not_le,
    implies_true]
  aesop
  exact lt_of_le_of_lt h left

theorem simple_boundary_path_proj_fst_Integrable {hl : Continuous L} : pathIntegral_proj_fst_Integrable R.a (R.b+1+R.b-R.a+1) L (simple_boundary_function R) := by

  have hct : Continuous R.f_t := by
    apply ContDiff.continuous R.t_contDiff

  have hcb : Continuous R.f_b := by
    apply ContDiff.continuous R.b_contDiff

  have h1 : R.b + 1 + R.b - R.a ≤ R.b + 1 + R.b - R.a := by
      rfl
  have h2 : R.b + 1 ≤ R.b + 1 + R.b - R.a := by
    rw [add_sub_assoc]
    apply le_add_of_le_of_nonneg
    rfl
    apply le_of_lt
    rw [sub_pos]
    exact R.a_lt_b
  have h3 : R.b ≤ R.b + 1 + R.b - R.a := by
    rw [add_sub_assoc]
    apply le_add_of_le_of_nonneg
    simp only [le_add_iff_nonneg_right, zero_le_one]
    apply le_of_lt
    rw [sub_pos]
    exact R.a_lt_b

  refine pathIntegral_proj_fst_Integrable_trans (c := R.b+1+R.b-R.a) ?_ ?_
  refine pathIntegral_proj_fst_Integrable_trans (c := R.b+1) ?_ ?_
  refine pathIntegral_proj_fst_Integrable_trans (c := R.b) ?_ ?_

  · let ff : ℝ → ℝ×ℝ := fun r ↦ (r, R.f_b r)
    have fcd : ContDiff ℝ 1 ff := by
      apply ContDiff.prod
      exact contDiff_id
      exact R.b_contDiff
    apply boundary_part_integrable R hct ff hcb R.a R.b R.a_lt_b _ (hl := hl)
    apply ContDiff.continuous_deriv (n := 1) fcd (le_refl 1)
    apply ContDiff.differentiable (n := 1) fcd (le_refl 1)

    unfold simple_boundary_function
    simp_rw [Set.eqOn_piecewise]
    rw [Ioo_inter_Iio_compl_self_right_eq_null]
    simp
    exact fun ⦃x⦄ ↦ congrFun rfl

 -- todo: maybe write a custom tactic for this intersection nonsense? -- if only i could work out how that would work
  · let ff : ℝ → ℝ×ℝ := fun r ↦ (R.b, R.f_b R.b + (r - R.b) * (R.f_t R.b - R.f_b R.b))
    have fcd : ContDiff ℝ 1 ff := by
      apply ContDiff.prod
      exact contDiff_const
      repeat first|apply contDiff_const_sub|apply contDiff_sub_const|apply contDiff_const_add|apply contDiff_const_mul
      exact contDiff_id

    apply boundary_part_integrable R hct ff hcb R.b (R.b + 1) _ _ (hl := hl)
    apply ContDiff.continuous_deriv (n := 1) fcd (le_refl 1)
    apply ContDiff.differentiable (n := 1) fcd (le_refl 1)
    exact lt_add_one R.b

    unfold simple_boundary_function
    simp_rw [Set.eqOn_piecewise]
    simp_rw [Set.inter_comm _ (Set.Iic (R.b + 1))ᶜ, <- Set.inter_assoc (Set.Iic (R.b + 1))ᶜ _, Set.inter_comm (Set.Iic (R.b + 1))ᶜ _]
    rw [Ioo_inter_Iic_self_left_eq_null, Ioo_inter_Iio_compl_self_right_eq_null]
    simp
    exact fun ⦃x⦄ ↦ congrFun rfl

  · let ff : ℝ → ℝ×ℝ := fun r ↦ (R.b + 1 + R.b - r, R.f_t (R.b + 1 + R.b - r))
    have fcd : ContDiff ℝ 1 ff := by
      apply ContDiff.prod
      apply ContDiff.sub
      exact contDiff_const
      exact contDiff_id
      apply ContDiff.comp
      exact R.t_contDiff
      apply ContDiff.sub
      exact contDiff_const
      exact contDiff_id

    apply boundary_part_integrable R hct ff hcb (R.b + 1) (R.b + 1 + R.b - R.a) _ _ (hl := hl)
    apply ContDiff.continuous_deriv (n := 1) fcd (le_refl 1)
    apply ContDiff.differentiable (n := 1) fcd (le_refl 1)
    have haa : (R.b + 1) + 0 = R.b + 1 := by
      simp
    nth_rw 1 [<- haa]
    rw [add_sub_assoc (R.b + 1)]
    apply add_lt_add_left
    rw [lt_sub_iff_add_lt]
    simp only [zero_add]
    exact R.a_lt_b

    unfold simple_boundary_function
    simp_rw [Set.eqOn_piecewise]
    simp_rw [Set.inter_comm _ (Set.Iic (R.b + 1)), <- Set.inter_assoc (Set.Iic (R.b + 1)) _, Set.inter_comm (Set.Iic (R.b + 1)) _]
    simp_rw [Set.inter_comm _ (Set.Iic (R.b + 1 + R.b - R.a))ᶜ, <- Set.inter_assoc (Set.Iic (R.b + 1 + R.b - R.a))ᶜ _, Set.inter_comm (Set.Iic (R.b + 1 + R.b - R.a))ᶜ _]
    rw [Ioo_inter_Iic_le_left_eq_null, Ioo_inter_Iic_le_left_eq_null, Ioo_inter_Iio_compl_self_right_eq_null]
    simp
    exact fun ⦃x⦄ ↦ congrFun rfl
    exact Preorder.le_refl (R.b + 1)
    simp

  · let ff : ℝ → ℝ×ℝ := fun r ↦ (R.a, R.f_t R.a - (r - (R.b + 1 + R.b - R.a)) * (R.f_t R.a - R.f_b R.a))
    have fcd : ContDiff ℝ 1 ff := by
      apply ContDiff.prod
      exact contDiff_const
      repeat first|apply contDiff_const_sub|apply contDiff_sub_const|apply contDiff_const_add|apply contDiff_const_mul
      exact contDiff_id

    apply boundary_part_integrable R hct ff hcb (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1) _ _ (hl := hl)
    apply ContDiff.continuous_deriv (n := 1) fcd (le_refl 1)
    apply ContDiff.differentiable (n := 1) fcd (le_refl 1)
    simp

    unfold simple_boundary_function
    simp_rw [Set.eqOn_piecewise]
    rw [Ioo_inter_Iic_le_left_eq_null]
    simp_rw [Set.inter_comm (Set.Ioo (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1)) _, Set.inter_assoc]
    rw [Ioo_inter_Iic_le_left_eq_null]
    simp_rw [Set.inter_comm (Set.Ioo (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1)) _, Set.inter_assoc]
    simp_rw [Set.inter_comm (Set.Iic (R.b + 1 + R.b - R.a))]
    rw [Ioo_inter_Iic_le_left_eq_null]
    simp
    exact fun ⦃x⦄ ↦ congrFun rfl
    exact h1
    exact h2
    exact h3

  done

end Region

namespace Green

open PathIntegral

variable {a b : ℝ} {f g : ℝ → ℝ}
variable {L : ℝ×ℝ → ℝ}
variable {k : ℝ → ℝ×ℝ}

theorem deriv_vec (k : ℝ → ℝ×ℝ) (x : ℝ) : deriv k x = (deriv (fun x ↦ (k x).1) x, deriv (fun x ↦ (k x).2) x) := by
  sorry -- unforch
  done

theorem green_split_alpha (s_0 s_1 s_2 s_3 s_4: ℝ) (hi : pathIntegral_proj_fst_Integrable s_0 s_4 L k) (hle01 : s_0 ≤ s_1) (hle12 : s_1 ≤ s_2) (hle23 : s_2 ≤ s_3) (hle34 : s_3 ≤ s_4) (hs01 : pathIntegral_proj_fst s_0 s_1 L k = ∫ x in a..b, L (x,g x)) (hs12 : pathIntegral_proj_fst s_1 s_2 L k = 0) (hs23 : pathIntegral_proj_fst s_2 s_3 L k = ∫ x in b..a, L (x,f x)) (hs30 : pathIntegral_proj_fst s_3 s_4 L k = 0) : pathIntegral_proj_fst s_0 s_4 L k = (∫ x in a..b, L (x,g x)) - ∫ x in a..b, L (x,f x) := by
  have hil : pathIntegral_proj_fst_Integrable s_0 s_2 L k := by
    apply pathIntegral_proj_fst_Integrable_on_union_left_reverse s_2 at hi
    exact hi
    exact Preorder.le_trans s_0 s_1 s_2 hle01 hle12
    exact Preorder.le_trans s_2 s_3 s_4 hle23 hle34

  have hir : pathIntegral_proj_fst_Integrable s_2 s_4 L k := by
    apply pathIntegral_proj_fst_Integrable_on_union_right_reverse s_2 at hi
    exact hi
    exact Preorder.le_trans s_0 s_1 s_2 hle01 hle12
    exact Preorder.le_trans s_2 s_3 s_4 hle23 hle34

  rw [<- pathIntegral_proj_fst_split_at s_1]
  nth_rw 2 [<- pathIntegral_proj_fst_split_at s_2]
  nth_rw 3 [<- pathIntegral_proj_fst_split_at s_3]
  rw [hs01, hs12, hs23, hs30, intervalIntegral.integral_symm a b]
  simp
  rfl
  · apply pathIntegral_proj_fst_Integrable_on_union_left_reverse s_3 at hir
    exact hir
    exact hle23
    exact hle34
  · apply pathIntegral_proj_fst_Integrable_on_union_right_reverse s_3 at hir
    exact hir
    exact hle23
    exact hle34
  · apply pathIntegral_proj_fst_Integrable_on_union_right_reverse s_1 at hil
    exact hil
    exact hle01
    exact hle12
  exact hir
  · apply pathIntegral_proj_fst_Integrable_on_union_left_reverse s_1 at hil
    exact hil
    exact hle01
    exact hle12
  · apply pathIntegral_proj_fst_Integrable_trans _ hir
    apply pathIntegral_proj_fst_Integrable_on_union_right_reverse s_1 at hil
    exact hil
    exact hle01
    exact hle12
  done

theorem green_split {R : Region.SimpleRegion a b f g } {hL : Continuous L} (a_eq_Ra : a = R.a) (b_eq_Rb : b = R.b) (f_eq_Rf : f = R.f_t) (g_eq_Rg : g = R.f_b) : pathIntegral_proj_fst R.a (R.b + 1 + R.b - R.a + 1) L (Region.simple_boundary_function R) = (∫ x in a..b, L (x,g x)) - ∫ x in a..b, L (x,f x) := by
  have hbi : pathIntegral_proj_fst_Integrable R.a (R.b+1+R.b-R.a+1) L (Region.simple_boundary_function R) := by
    apply Region.simple_boundary_path_proj_fst_Integrable
    exact hL
  apply green_split_alpha R.a R.b (R.b + 1) (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1)
  all_goals first|simp [R.a_lt_b, le_of_lt]|skip
  swap
  · apply le_of_lt
    simp_rw [add_sub_assoc, add_assoc]
    simp
    exact R.a_lt_b
  exact hbi
  · unfold pathIntegral_proj_fst
    simp
    suffices : ∀ x, (deriv (fun r ↦ (r, R.f_b r)) x).1 = 1
    · rw [intervalIntegral.integral_congr_ae (g := (fun r ↦ L (r, R.f_b r) * (deriv (fun r ↦ (r, R.f_b r)) r).1))]
      simp_all

      rw [Set.uIoc, min_def, max_def]
      have rble : R.a ≤ R.b := by
        apply le_of_lt
        exact R.a_lt_b
      simp [rble]
      unfold Region.simple_boundary_function
      simp_rw [Set.apply_piecewise _ _ _ (fun r ↦ L)]
      have x_gt (x : ℝ) (h : x ∈ Set.Ioc (R.b + 1) (R.b + 1 + R.b - R.a)) : (R.b + 1) < x := by
        simp_all only [Set.mem_Ioc]
      have t2 (x : ℝ) : (R.b + 1) < x → x ∉ Set.Iic (R.b) := by
        intro a_1
        simp
        apply lt_of_add_lt_of_nonneg_left (b := 1)
        exact a_1
        exact zero_le_one
      conv => congr; intro x x_1 x_2; rw [Set.piecewise_eq_of_mem]; rfl; exact x_2; rfl
      simp_rw [mul_eq_mul_left_iff]
      -- so then, the last* piece of the puzzle - getting 'for almost all' into 'almost everywhere equal' while keeping the condition on x
      -- * the other being however one could deal with deriv_vec
      simp_rw [<- and_imp, <- Set.mem_Ioc]
      apply MeasureTheory.ae_imp_of_ae_restrict
      rw [Filter.Eventually]
      have (x : ℝ) (f g : ℝ → ℝ) : f =ᵐ[MeasureTheory.volume.restrict (Set.Ioc R.a R.b)] g → {x | f x = g x} ∈ MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioc R.a R.b)) := by
        intro a_1
        simp_all only [Set.mem_Ioc, implies_true, Set.mem_Iic, not_le, measurableSet_Ioc,
          MeasureTheory.ae_restrict_eq]
        exact a_1
      -- have (x : ℝ) (q q2 : ℝ → Prop) : {x | q x} → {x | q x ∨ q2 x} := by
      --   intro a_1
      --   simp_all only [Set.mem_Ioc, implies_true, Set.mem_Iic, not_le, measurableSet_Ioc,
      --     MeasureTheory.ae_restrict_eq, forall_const, Set.coe_setOf]
      --   obtain ⟨val, property⟩ := a_1
      --   simp_all only [Set.mem_setOf_eq]
      --   apply Subtype.mk
      --   · apply Or.inl
      --     exact property -- yek what -- aesop ofc

      -- conv => congr; congr; rfl; congr; intro x; tactic => apply Or.inl; apply Or.intro_left _ (L (x, R.f_b x) = 0);
      have ad : ({x |
    (deriv
            ((Set.Iic R.b).piecewise (fun r ↦ (r, R.f_b r))
              ((Set.Iic (R.b + 1)).piecewise (fun r ↦ (R.b, R.f_b R.b + (r - R.b) * (R.f_t R.b - R.f_b R.b)))
                ((Set.Iic (R.b + 1 + R.b - R.a)).piecewise (fun r ↦ (R.b + 1 + R.b - r, R.f_t (R.b + 1 + R.b - r)))
                  fun r ↦ (R.a, R.f_t R.a - (r - (R.b + 1 + R.b - R.a)) * (R.f_t R.a - R.f_b R.a)))))
            x).1 =
        (deriv (fun r ↦ (r, R.f_b r)) x).1} ∈
  MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioc R.a R.b))) → ({x |
    (deriv
            ((Set.Iic R.b).piecewise (fun r ↦ (r, R.f_b r))
              ((Set.Iic (R.b + 1)).piecewise (fun r ↦ (R.b, R.f_b R.b + (r - R.b) * (R.f_t R.b - R.f_b R.b)))
                ((Set.Iic (R.b + 1 + R.b - R.a)).piecewise (fun r ↦ (R.b + 1 + R.b - r, R.f_t (R.b + 1 + R.b - r)))
                  fun r ↦ (R.a, R.f_t R.a - (r - (R.b + 1 + R.b - R.a)) * (R.f_t R.a - R.f_b R.a)))))
            x).1 =
        (deriv (fun r ↦ (r, R.f_b r)) x).1 ∨
      L (x, R.f_b x) = 0} ∈
  MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioc R.a R.b))) := by
        sorry
      apply ad
      apply this
      simp_all only [Set.mem_Ioc, implies_true, Set.mem_Iic, not_le, measurableSet_Ioc, MeasureTheory.ae_restrict_eq,
        forall_const]
      exact a --aesop again, idrek what or why, apparently this shows 'R'
      have (f g : ℝ → ℝ×ℝ) : (f =ᵐ[MeasureTheory.volume.restrict (Set.Ioc R.a R.b)] g) → (fun x ↦ (f x).1) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc R.a R.b)] fun x ↦ (g x).1 := by
        sorry
      apply this
      -- apply deriv_piecewise_Ioo_of_lt -- this was before i changed the interval ends around
      -- you get the idea tho
      -- should be basically the exact same for the other 3 segments assuming the other sorries can be filled in
      -- as it is, I have run out of time despite spending far longer than i really should have, and haven't even optimised anything
      -- (I looked into trying some meta programming but i couldn't really figure it out, and like what's wrong with the 4 sledgehammers I'm using already)
      sorry


      -- conv => congr; intro x x_1; rw [congr_arg Prod.fst (a₂ := (deriv (fun r ↦ (r, R.f_b r)) x))]; rfl; tactic => sorry
      -- simp
    · intro x
      rw [deriv_vec]
      simp only [deriv_const']
      simp
  · unfold pathIntegral_proj_fst
    unfold intervalIntegral
    simp
    suffices : ∀ x, (deriv (fun r ↦ (R.b, R.f_b R.b + (r - R.b) * (R.f_t R.b - R.f_b R.b))) x).1 = 0
    · rw [MeasureTheory.setIntegral_congr_ae (g := (fun r ↦ L (R.b, R.f_b R.b + (r - R.b) * (R.f_t R.b - R.f_b R.b)) * (deriv (fun r ↦ (R.b, R.f_b R.b + (r - R.b) * (R.f_t R.b - R.f_b R.b))) r).1))]
      simp_all only [abs_zero, mul_zero, MeasureTheory.integral_zero]
      exact measurableSet_Ioc
      unfold Region.simple_boundary_function
      simp_rw [Set.apply_piecewise _ _ _ (fun r ↦ L)]
      have t : ∀ x, x ∈ Set.Ioc R.b (R.b + 1) → x ∉ Set.Iic R.b := by
        intro x a_1
        simp_all only [Set.mem_Ioc, Set.mem_Iic, not_le]
      -- ngl idk how the rfl to cut out the first bit works
      conv => congr; intro x x_1; rw [Set.piecewise_eq_of_not_mem, Set.piecewise_eq_of_mem]; rfl; exact Set.mem_of_mem_inter_right x_1; apply t; exact x_1; rfl
      simp_rw [mul_eq_mul_left_iff]
      -- this is where i need the ae
      -- this conv doesn't actually work since it gets rid of the ae but is a placeholder
      conv => congr; intro x x_1; rw [congr_arg Prod.fst (a₂ := (deriv (fun r ↦ (R.b, R.f_b R.b + (r - R.b) * (R.f_t R.b - R.f_b R.b))) x))]; rfl; tactic => sorry
      simp
    · intro x
      -- nah i basically have to work out how to take projection into the deriv
      -- maybe i actually just have to define that that's how deriv works in this case?
      rw [deriv_vec]
      simp only [deriv_const']

  · unfold pathIntegral_proj_fst
    simp
    suffices : ∀ x, (deriv (fun r ↦ (R.b + 1 + R.b - r, R.f_t (R.b + 1 + R.b - r))) x).1 = -1
    · rw [intervalIntegral.integral_congr_ae (g := (fun r ↦ L (R.b + 1 + R.b - r, R.f_t (R.b + 1 + R.b - r)) * (deriv (fun r ↦ (R.b + 1 + R.b - r, R.f_t (R.b + 1 + R.b - r))) r).1))]
      simp_all
      have newL (x : ℝ) : L (R.b + 1 + R.b - x, R.f_t (R.b + 1 + R.b - x)) = (fun r ↦ L (r, R.f_t r)) ((R.b + 1 + R.b) - x) := by
        simp
      conv => congr; congr; congr; intro x; rw [newL]
      rw [intervalIntegral.integral_comp_sub_left (fun r ↦ L (r, R.f_t r)) (R.b + 1 + R.b)]
      simp
      rw [<- intervalIntegral.integral_symm]
      rw [Set.uIoc, min_def, max_def]
      have rble : R.b + 1 ≤ R.b + 1 + R.b - R.a := by
        rw [add_sub_assoc]
        simp
        apply le_of_lt
        exact R.a_lt_b
      simp [rble]
      unfold Region.simple_boundary_function
      simp_rw [Set.apply_piecewise _ _ _ (fun r ↦ L)]
      have x_gt (x : ℝ) (h : x ∈ Set.Ioc (R.b + 1) (R.b + 1 + R.b - R.a)) : (R.b + 1) < x := by
        simp_all only [Set.mem_Ioc]
      have t2 (x : ℝ) : (R.b + 1) < x → x ∉ Set.Iic (R.b) := by
        intro a_1
        simp
        apply lt_of_add_lt_of_nonneg_left (b := 1)
        exact a_1
        exact zero_le_one
      conv => congr; intro x x_1 x_2; rw [Set.piecewise_eq_of_not_mem, Set.piecewise_eq_of_not_mem, Set.piecewise_eq_of_mem]; rfl; exact x_2; exact Set.not_mem_Iic.mpr x_1; apply t2; exact x_1; rfl
      simp_rw [mul_eq_mul_left_iff]
      conv => congr; intro x x_1; rw [congr_arg Prod.fst (a₂ := (deriv (fun r ↦ (R.b + 1 + R.b - r, R.f_t (R.b + 1 + R.b - r))) x))]; rfl; tactic => sorry
      simp
    · intro x
      rw [deriv_vec]
      simp only [deriv_const']
      rw [deriv_sub]
      simp
      simp
      simp
  · unfold pathIntegral_proj_fst
    unfold intervalIntegral
    simp
    suffices : ∀ x, (deriv (fun r ↦ (R.a, R.f_t R.a - (r - (R.b + 1 + R.b - R.a)) * (R.f_t R.a - R.f_b R.a))) x).1 = 0
    · rw [MeasureTheory.setIntegral_congr_ae (g := (fun r ↦ L (R.a, R.f_t R.a - (r - (R.b + 1 + R.b - R.a)) * (R.f_t R.a - R.f_b R.a)) * (deriv (fun r ↦ (R.a, R.f_t R.a - (r - (R.b + 1 + R.b - R.a)) * (R.f_t R.a - R.f_b R.a))) r).1))]
      simp_all only [abs_zero, mul_zero, MeasureTheory.integral_zero]
      exact measurableSet_Ioc
      unfold Region.simple_boundary_function
      simp_rw [Set.apply_piecewise _ _ _ (fun r ↦ L)]
      have x_gt (x : ℝ) (h : x ∈ Set.Ioc (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1)) : (R.b + 1 + R.b - R.a) < x := by
        simp_all only [Set.mem_Ioc]
      have t (x : ℝ) : x ∈ Set.Ioc (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1) → x ∉ Set.Iic (R.b + 1 + R.b - R.a) := by
        intro a_1
        simp_all only [Set.mem_Ioc, Set.mem_Iic, not_le]
      have t2 (x : ℝ) : x ∈ Set.Ioc (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1) → x ∉ Set.Iic (R.b + 1) := by
        intro a_1
        simp
        apply lt_trans _ (x_gt x a_1)
        simp only [add_sub_assoc, lt_add_iff_pos_right, sub_pos, R.a_lt_b]
      have t3 (x : ℝ) : x ∈ Set.Ioc (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1) → x ∉ Set.Iic (R.b) := by
        intro a_1
        simp
        apply lt_trans _ (x_gt x a_1)
        rw [add_sub_assoc]
        apply lt_add_of_lt_of_pos'
        simp
        simp only [sub_pos, R.a_lt_b]
      conv => congr; intro x x_1; rw [Set.piecewise_eq_of_not_mem, Set.piecewise_eq_of_not_mem, Set.piecewise_eq_of_not_mem]; rfl; apply t; exact x_1; apply t2; exact x_1; apply t3; exact x_1; rfl
      simp_rw [mul_eq_mul_left_iff]
      conv => congr; intro x x_1; rw [congr_arg Prod.fst (a₂ := (deriv (fun r ↦ (R.a, R.f_t R.a - (r - (R.b + 1 + R.b - R.a)) * (R.f_t R.a - R.f_b R.a))) x))]; rfl; tactic => sorry
      simp
    · intro x
      rw [deriv_vec]
      simp only [deriv_const']
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
