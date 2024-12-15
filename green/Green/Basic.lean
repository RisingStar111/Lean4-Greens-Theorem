import Mathlib.Tactic

#allow_unused_tactic Lean.Parser.Tactic.done

namespace PathIntegral

open MeasureTheory

variable [NormedSpace ℝ ℝ] -- can generalise second R to a normedaddcommgroup or something judging by the definitions
variable {a b : ℝ} {f g : ℝ → ℝ} {μ : Measure ℝ}
variable {L : ℝ×ℝ → ℝ}
variable {k : ℝ → ℝ×ℝ}
-- variable {p1 p2 : ℝ×ℝ}

-- todo: update the notation syntax to lean 4, and also like get the second one to work idk
-- notation3"∫ "(...)" in "a", "p:60:(scoped f => f)" ∂"μ:70 => pathIntegral p a μ
-- notation3"∫ "(...)" in "a", "p:60:(scoped f => pathIntegral f a volume) => a

noncomputable
def pathIntegral_proj_fst (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : Measure ℝ := volume) : ℝ :=
  ∫ x in a..b, (fun x ↦ (f (r x)) * norm ((deriv r x).fst)) x ∂μ

variable [IsLocallyFiniteMeasure μ] -- not sure why this behaves differently to putting it in the assumptions wrt the thms after it's ommitted

def pathIntegral_proj_fst_Integrable (a b : ℝ) (f : ℝ×ℝ → ℝ) (r : ℝ → ℝ×ℝ) (μ : Measure ℝ := volume) : Prop :=
  IntervalIntegrable (fun x ↦ (f (r x)) * norm ((deriv r x).fst)) μ a b

theorem pathIntegral_proj_fst_Integrable_translate_zero (hi : pathIntegral_proj_fst_Integrable a b L k MeasureTheory.volume) : pathIntegral_proj_fst_Integrable 0 (b-a) L (fun x ↦ k (x+a)) MeasureTheory.volume := by
  have haa : a - a = 0 := by
    simp
  unfold pathIntegral_proj_fst_Integrable
  simp_rw [<- haa, deriv_comp_add_const]
  have : (fun x ↦ L (k (x + a)) * ‖(deriv k (x + a)).1‖) = fun x ↦ ((fun x ↦ L (k (x)) * ‖(deriv k (x)).1‖) (x + a)) := by
    rfl
  rw [this]
  apply IntervalIntegrable.comp_add_right (f := (fun x ↦ L (k (x)) * ‖(deriv k (x)).1‖))-- not sure what complicated this so much
  exact hi
  done

theorem norm_continuous_pathIntegral_proj_fst_intervalIntegrable {hl : Continuous L} {hk : Continuous k} {hdk : Continuous (fun x ↦ ‖(deriv k x).fst‖)} : pathIntegral_proj_fst_Integrable a b L k μ := by
  refine Continuous.intervalIntegrable ?h a b
  -- continuity
  apply Continuous.mul
  exact Continuous.comp' hl hk
  exact hdk
  done

theorem congr_ae_norm_continuous_pathIntegral_proj_fst_intervalIntegrable_Ioo [NoAtoms μ] {hab : a ≤ b} {hl : Continuous L} {hk : Continuous k} (o : ℝ → ℝ×ℝ) (hdo : Continuous (fun x ↦ ‖(deriv o x).fst‖)) (hst : Set.EqOn (fun x ↦ ‖(deriv k x).fst‖) (fun x ↦ ‖(deriv o x).fst‖) (Set.Ioo a b)) : pathIntegral_proj_fst_Integrable a b L k μ := by
  unfold pathIntegral_proj_fst_Integrable
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]

  suffices IntegrableOn (fun x ↦ L (k x) * ‖(deriv o x).1‖) (Set.Ioo a b) μ by
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

-- a third potential option
theorem zip_piecewise {s : Set ℝ} [(j : ℝ) → Decidable (j ∈ s)] {q r : ℝ → ℝ}: s.piecewise f g * s.piecewise q r = s.piecewise (f * q) (g * r) := by
  exact Eq.symm (Set.piecewise_mul s f q g r)
theorem zip_piecewise_deriv {s : Set ℝ} [(j : ℝ) → Decidable (j ∈ s)]: s.piecewise f g * s.piecewise (deriv f) (deriv g) = s.piecewise (f * (deriv f)) (g * (deriv g)) := by
  exact zip_piecewise
theorem deriv_piecewise {s : Set ℝ} [(j : ℝ) → Decidable (j ∈ s)] : deriv (s.piecewise f g) = s.piecewise (deriv f) (deriv g) := by
   -- t'would be great but i suppose it's not technically true due to the derivitive not being defined at the crossing
  -- since i'm only using it in an integral i can make do with ae equal if that helps
  -- apply integral_piecewise -- right looking at this -- who could have guessed, quite helpful -- new technique unlocked
  -- rw [<- Set.indicator_add_compl_eq_piecewise]
  -- -- rw [deriv_add] -- i hate deriv ngl
  funext x
  -- have : s.indicator f + sᶜ.indicator g = fun x ↦ (s.indicator f x + sᶜ.indicator g x) := by
  --   rfl
  -- rw [this, deriv_add] -- tbh no wonder i didn't work it out before
  -- revert x
  -- rw [<- funext_iff]
  -- nvm this isn't helpful cuz the derivative of an indicator obviously doesn't exist and i still can't get the indicator out
  -- unfold Set.indicator
  -- have : HasDerivWithinAt (s.piecewise f g) (derivWithin f s x) s x := by
  --   apply HasFDerivWithinAt.congr' (f := f)
  --   simp only [hasDerivWithinAt_derivWithin_iff]
  --   sorry
  --   exact fun x a ↦ Set.piecewise_eq_of_mem s f g a
  --   exact?

theorem zip_piecewise_in_deriv {s : Set ℝ} [(j : ℝ) → Decidable (j ∈ s)]: s.piecewise f g * deriv (s.piecewise f g) = s.piecewise (f * (deriv f)) (g * (deriv g)) := by
  apply

theorem asdasd {hab : a ≤ b} : ∫ x in a..b, ((Set.Ico a b).piecewise f g) x =  ∫ x in a..b, f x:= by
  unfold intervalIntegral
  aesop
  apply Measure.restrict_apply
  conv => lhs; congr; rfl; rw [Set.piecewise_eq_of_mem]

-- a different potential option
theorem bounds_inside_intervalIntegral {hab : a ≤ b} {hac : IntervalIntegrable f μ a b} : ∫ x in a..b, (fun x ↦ if x ∈ (Set.Ioc a b) then f x else 0) x ∂μ = ∫ x in a..b, f x ∂μ := by
  unfold intervalIntegral
  simp_all only [Set.mem_Ioc, not_lt, Set.Ioc_eq_empty, Measure.restrict_empty, integral_zero_measure, sub_zero]
  simp_rw [integral_def]
  have cr : CompleteSpace ℝ := by
    exact Real.instCompleteSpace
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le] at hac
  unfold IntegrableOn at hac
  simp [cr, hac, ↓reduceDIte]
  apply integral_piecewise
  sorry
  done
-- not quite what's needed as it can only split once but should be easier to start from
theorem pathIntegral_proj_fst_split_at_restrict (c : ℝ) {hac : pathIntegral_proj_fst_Integrable a c L k μ} {hcb : pathIntegral_proj_fst_Integrable c b L k μ} : pathIntegral_proj_fst a c L (fun x ↦ if x < c then k x else 0) μ + pathIntegral_proj_fst c b L (fun x ↦ if c ≤ x then k x else 0) μ = pathIntegral_proj_fst a b L k μ := by
  nth_rw 3 [<- pathIntegral_proj_fst_split_at c]
  · unfold pathIntegral_proj_fst
    unfold intervalIntegral
    simp_rw [integral_def] -- ...
    have cr : CompleteSpace ℝ := by
      exact Real.instCompleteSpace
    simp [cr, ↓reduceDIte]
  exact hac
  exact hcb
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
  Set.piecewise (Set.Iio R.b) (fun r ↦ (r, R.f_b r))
    (Set.piecewise (Set.Iio (R.b+1)) (fun r ↦ (R.b, (R.f_b R.b) + (r - R.b) * (R.f_t R.b - R.f_b R.b)))
      (Set.piecewise (Set.Iio (R.b+1+R.b-R.a)) (fun r ↦ (R.b+1+R.b - r, R.f_t (R.b+1+R.b - r)))
        (fun r ↦ (R.a, (R.f_t R.a) - (r-(R.b+1+R.b-R.a)) * (R.f_t R.a - R.f_b R.a)))))

theorem simple_boundary_continuous (hct : Continuous R.f_t) (hcb : Continuous R.f_b) : Continuous (simple_boundary_function R) := by
  unfold simple_boundary_function
  apply Continuous.piecewise
  simp
  continuity

  apply Continuous.piecewise
  simp_rw [Set.piecewise.eq_1]
  simp
  simp_rw [add_sub_assoc, lt_add_iff_pos_right, sub_pos, R.a_lt_b, reduceIte]

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

theorem Ioo_inter_Ici_of_le {a b c : ℝ} (h : c ≤ a): Set.Ioo a b ∩ Set.Ici c = Set.Ioo a b := by
  simp only [Set.inter_eq_left]
  rw [Set.Ioo, Set.Ici]
  simp_all only [Set.setOf_subset_setOf, and_imp]
  intro a_1 a_2 a_3
  apply le_of_lt
  exact lt_of_le_of_lt h a_2
  done

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

-- don't actually need this? just the separate parts since it's constructivist in green's anyway atm, tho good isolated test (also idk if trans works backwards)
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
  -- need continuity within set implies integrable on that set, using Ico (oh needs bounded too)
  -- can't see a way to do above (maybe filters? but idk how to work with those at all) so arclength it is
  -- ah hmm i can convert interval integrability -> measure integrability -> use their lemmas on removing/adding endpoints
  -- but that's only got atfilter for from continuous functions...
  -- need boundary is continuously diffable on piecewises
  -- this is actually where using paths instead of explicit funtions could be helpful

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
    rw [<- min_self R.b, <- Set.Ioo_inter_Iio (a := R.a) (b := R.b) (c := R.b), min_self]
    simp_rw [Set.inter_assoc _ (Set.Iio R.b), Set.inter_compl_self (Set.Iio R.b)]
    -- mostly aesop
    simp_all only [differentiable_id', Set.inter_self, Set.inter_empty, Set.empty_inter, Set.eqOn_empty, Set.compl_Iio, and_self, and_true]
    exact fun ⦃x⦄ ↦ congrFun rfl

 -- todo: maybe write a custom tactic for this intersection nonsense?
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
    rw [<- min_self (R.b + 1), <- Set.Ioo_inter_Iio (a := R.b) (b := R.b + 1) (c := R.b + 1), min_self]
    simp_rw [Set.inter_assoc _ (Set.Iio (R.b + 1)), Set.inter_comm (Set.Iio (R.b + 1)), Set.inter_assoc _ _ (Set.Iio (R.b + 1))ᶜ, Set.inter_compl_self (Set.Iio (R.b + 1)), Set.Iio_inter_Iio, Set.Ioo_inter_Iio]
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
    rw [<- min_self (R.b + 1 + R.b - R.a), <- Set.Ioo_inter_Iio (a := (R.b + 1)) (b := (R.b + 1 + R.b - R.a)) (c := (R.b + 1 + R.b - R.a)), min_self]
    -- there has to be a better way to do this
    simp_rw [Set.inter_assoc, Set.inter_comm (Set.Iio (R.b + 1 + R.b - R.a)), Set.inter_assoc, Set.inter_comm, Set.inter_compl_self (Set.Iio (R.b + 1 + R.b - R.a)), Set.Iio_inter_Iio, Set.inter_assoc, Set.Iio_inter_Ioo]
    simp
    exact fun ⦃x⦄ ↦ congrFun rfl

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

    simp_rw [Set.compl_Iio]
    rw [Ioo_inter_Ici_of_le h3]
    rw [Ioo_inter_Ici_of_le h2]
    rw [Ioo_inter_Ici_of_le h1]
    simp_rw [Set.Ioo_inter_Iio, Set.eqOn_refl]
    aesop -- ok this is actually better at least to look at

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

theorem green_split_alpha (s_0 s_1 s_2 s_3 s_4: ℝ) (hi : pathIntegral_proj_fst_Integrable s_0 s_4 L k) (hle01 : s_0 ≤ s_1) (hle12 : s_1 ≤ s_2) (hle23 : s_2 ≤ s_3) (hle34 : s_3 ≤ s_4) (hs01 : pathIntegral_proj_fst s_0 s_1 L k = ∫ x in a..b, L (x,f x)) (hs12 : pathIntegral_proj_fst s_1 s_2 L k = 0) (hs23 : pathIntegral_proj_fst s_2 s_3 L k = ∫ x in b..a, L (x,g x)) (hs30 : pathIntegral_proj_fst s_3 s_4 L k = 0) : pathIntegral_proj_fst s_0 s_4 L k = (∫ x in a..b, L (x,f x)) - ∫ x in a..b, L (x,g x) := by
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

theorem green_split {R : Region.SimpleRegion a b f g } {hL : Continuous L} : pathIntegral_proj_fst R.a (R.b + 1 + R.b - R.a + 1) L (Region.simple_boundary_function R) = (∫ x in a..b, L (x,f x)) - ∫ x in a..b, L (x,g x) := by
  have hbi : pathIntegral_proj_fst_Integrable R.a (R.b+1+R.b-R.a+1) L (Region.simple_boundary_function R) := by
    apply Region.simple_boundary_path_proj_fst_Integrable
    exact hL
  -- apply pathIntegral_proj_fst_Integrable_translate_zero at hbi
  apply green_split_alpha R.a R.b (R.b + 1) (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1)
  all_goals first|simp [R.a_lt_b, le_of_lt]|skip
  swap
  · apply le_of_lt
    simp_rw [add_sub_assoc, add_assoc]
    simp
    exact R.a_lt_b
  exact hbi
  · sorry
  · unfold pathIntegral_proj_fst
    unfold intervalIntegral
    simp
    unfold Region.simple_boundary_function
    suffices : ∀ x, (deriv (fun r ↦ (R.b, R.f_b R.b + (r - R.b) * (R.f_t R.b - R.f_b R.b))) x).1 = 0
    · --apply MeasureTheory.integral_piecewise
      -- simp_rw [Set.piecewise_eq_of_mem (Set.Iio R.b) (fun r ↦ (r, R.f_b r))]
      simp_rw [deriv_vec]
      sorry -- this is also rather an issue huh
      -- regardless of what i do i'm pretty sure i need to be able to use the bounds of the integral to simplify the function but idk how
      -- maybe a better option is to drag the condition on x into the function when the integral is split - ofc i still need to work out how to do it but then it's just working on a general function
    · intro x
      -- nah i basically have to work out how to take projection into the deriv
      -- maybe i actually just have to define that that's how deriv works in this case?
      rw [deriv_vec]
      simp only [deriv_const']

  · sorry
  · sorry
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
