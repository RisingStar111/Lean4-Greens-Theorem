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
  -- let ff := (fun x ↦ L (k (x)) * ‖(deriv k (x)).1‖)
  -- generalize (fun x ↦ L (k (x)) * ‖(deriv k (x)).1‖) = ff
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
-- since above is still too strong

-- theorem mul_congr_ae_func (s : Set ℝ) (q : ℝ → ℝ) (hg : f =ᶠ[ae (μ.restrict s)] g) : (fun x ↦ q x * f x) =ᶠ[ae (μ.restrict s)] (fun x ↦ q x * g x) := by
--   apply Filter.EventuallyEq.mul _ hg
--   rfl
--   done

-- theorem congr_ae_norm_continuous_pathIntegral_proj_fst_intervalIntegrable_Ioc [NoAtoms μ] {hab : a ≤ b} {hl : Continuous L} {hk : Continuous k} (o : ℝ → ℝ×ℝ) (hdo : Continuous (fun x ↦ ‖(deriv o x).fst‖)) (hst : (fun x ↦ ‖(deriv k x).fst‖) =ᵐ[μ.restrict (Set.Ico a b)] (fun x ↦ ‖(deriv o x).fst‖)) : pathIntegral_proj_fst_Integrable a b L k μ := by
theorem congr_ae_norm_continuous_pathIntegral_proj_fst_intervalIntegrable_Ioo [NoAtoms μ] {hab : a ≤ b} {hl : Continuous L} {hk : Continuous k} (o : ℝ → ℝ×ℝ) (hdo : Continuous (fun x ↦ ‖(deriv o x).fst‖)) (hst : Set.EqOn (fun x ↦ ‖(deriv k x).fst‖) (fun x ↦ ‖(deriv o x).fst‖) (Set.Ioo a b)) : pathIntegral_proj_fst_Integrable a b L k μ := by
  -- was having a lot of trouble getting it to know that Set.Ico is a Set R
  -- apparently the problem was that i was delaying that definition to a variable, and then it was tryingto coerce it but couldn't

  unfold pathIntegral_proj_fst_Integrable
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]

  suffices IntegrableOn (fun x ↦ L (k x) * ‖(deriv o x).1‖) (Set.Ioo a b) μ by
    apply IntegrableOn.congr_fun this
    exact fun ⦃x⦄ a_1 ↦ congrArg (HMul.hMul (L (k x))) (id (Set.EqOn.symm hst) a_1) -- apply? moment
    exact measurableSet_Ioo
  -- suffices IntegrableOn (fun x ↦ L (k x) * ‖(deriv o x).1‖) (Set.Ico a b) μ by
  --   -- look what i found
  --   apply IntegrableOn.congr_fun_ae this (f := (fun x ↦ L (k x) * ‖(deriv o x).1‖))
  --   apply Filter.EventuallyEq.mul
  --   simp only [ae_restrict_eq, Filter.EventuallyEq.refl]
  --   apply Filter.EventuallyEq.symm hst
    -- can't even multiple by a thing - granted this is somewhat fair but the thing is nice to multiply by
    -- not even a chance tho
    -- all this to not even (yet) avoid a condition on the gradient of the boundary function at the corners
    -- ~~a condition that is always achievable given the constraints~~
    -- sorry

  rw [<- integrableOn_Icc_iff_integrableOn_Ioo]
  apply Continuous.integrableOn_Icc
  apply Continuous.mul
  continuity
  assumption
  -- refine Continuous.intervalIntegrable ?h a b
  -- apply Continuous.mul
  -- exact Continuous.comp' hl hk
  -- exact hdk
  done
  -- all came together in the end, nice
  -- remains to be seen if i can actually utilise this

-- so (looking at how intervalintegral does it) i actually needed to be looking at 'function.locallyintegrable' ofc yes that makes sense
-- variable [NoAtoms μ]
-- theorem intervalIntegral_of_continuous_on_Ico {hab : a ≤ b}: IntervalIntegrable f μ a b := by
--   rw [intervalIntegrable_iff_integrableOn_Ico_of_le]
--   rw [<- integrableOn_Icc_iff_integrableOn_Ico]
--   apply ContinuousOn.integrableOn_Icc
--   sorry
--   done

-- ok *now* i'm fairly confident what i actually actually need is MeasureTheory.IntegrableOn.congr_fun_ae
-- but with this probably easiest to work with the explicit function
-- similar but can use above and iff unrestriction integrable
-- theorem intervalIntegral_of_bounded_continuous_on_Ico {hab : a ≤ b}: IntervalIntegrable f μ a b := by

--   sorry
--   done

omit [IsLocallyFiniteMeasure μ]

-- seems like this should work but intervalIntegable works with Icc, which this obviously won't be
-- so back to arclength param :(
-- theorem pathIntegral_proj_fst_Integrable_of_continuous_within_at {c : ℝ} (hac : pathIntegral_proj_fst_Integrable a c L k μ) (hcb : pathIntegral_proj_fst_Integrable c b L k μ) : pathIntegral_proj_fst_Integrable a b L k μ := by
--   unfold pathIntegral_proj_fst_Integrable
--   apply IntervalIntegrable.continuousOn_mul
--   done

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

-- theorem aa (f : ℝ → ℝ): Continuous (deriv f) → ContDiff ℝ 1 f := by
--   intro a
--   apply contDiff_one_iff_deriv.mpr
--   apply And.intro

-- theorem ab (f : ℝ → ℝ) : ∀x, (deriv (fun r ↦ (Prod.mk r (f r))) x) = (1, deriv f x) := by
--   intro x
--   -- apply Prod.ext
--   -- simp
--   apply deriv_finset_prod
--   apply Prod.
--   refine HasDerivAt.deriv ?h
--   apply HasDerivAt.finset_prod

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
  -- apply Continuous.norm
  -- -- wait the x component of the deriv of the horiz is always 1...
  -- -- doesn't matter cuz i can't work out how to manipulate the deriv into the product
  -- apply Continuous.fst
  continuity
  apply Set.EqOn.comp_left
  apply Set.EqOn.comp_left

  -- have : ∀ x ∈ (Set.Ico R.a R.b), deriv (simple_boundary_function R) x = deriv (fun r ↦ (r, R.f_b r)) x := by
  --   -- aesop
  --   intro x h
  --   refine Filter.EventuallyEq.deriv_eq ?hL
  --   unfold simple_boundary_function


  --   done

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

  -- apply Set.EqOn
  -- unfold Set.EqOn
  -- -- rw [congrArg deriv]
  -- -- pick_goal 3
  -- -- use simple_boundary_function R
  -- -- swap; rfl
  -- intro x a_1
  -- simp_all only [Set.mem_Ico]
  -- obtain ⟨left, right⟩ := a_1 -- idk what all this is, aesop. probably useful to know tho, like congrArg
  -- unfold simple_boundary_function
  -- apply congrArg
  -- rw [congrArg deriv] -- this eats the x dependance
  -- apply Set.piecewise_

  -- apply Filter.EventuallyEq.fun_comp
  -- apply Filter.EventuallyEq.fun_comp
  -- unfold simple_boundary_function


  -- let jj : ℕ → ℝ → ℝ :=
  --   fun x ↦ (if x = 1 then fun x ↦ x else fun x ↦ R.f_b x)

  -- have : ∏ i ∈ {0,1}, jj i = fun x ↦ (x, R.f_b x) := by


  -- apply contDiff_prod
  -- apply contDiff_one_iff_deriv
  -- have : deriv (fun x ↦ (R.f_b x, R.f_b x)) = fun x ↦ (deriv R.f_b x, deriv R.f_b x) := by
  --   simp
  -- apply deriv_comp

  -- suffices MeasureTheory.IntegrableOn (fun x ↦ ‖(deriv (simple_boundary_function R) x).1‖) (Set.Ico a b) by
  --   apply norm_continuous_pathIntegral_proj_fst_intervalIntegrable (hl := hl) (hk := hr)
  --   unfold pathIntegral_proj_fst_Integrable
  --   apply intervalIntegrable_iff.mpr
  -- suffices ContinuousOn (fun x ↦ ‖(deriv (simple_boundary_function R) x).1‖) (Set.Ico a b) by

  -- unfold pathIntegral_proj_fst_Integrable
  apply hse
  -- unfold simple_boundary_function
  -- simp_rw [Set.eqOn_piecewise]
  -- rw [<- min_self R.b ,<- Set.Ioo_inter_Iio (a := R.a) (b := R.b) (c := R.b), min_self]
  -- simp_rw [Set.inter_assoc _ (Set.Iio R.b), Set.inter_compl_self (Set.Iio R.b)]
  -- -- mostly aesop
  -- simp_all only [differentiable_id', Set.inter_self, Set.inter_empty, Set.empty_inter, Set.eqOn_empty, Set.compl_Iio, and_self, and_true]
  -- exact fun ⦃x⦄ ↦ congrFun rfl
  -- that was one (and the easiest) case lmao

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

theorem Ioo_inter_Ici_of_le {a b c : ℝ} (h : c ≤ a): Set.Ioo a b ∩ Set.Ici c = Set.Ioo a b := by
  simp only [Set.inter_eq_left]
  rw [Set.Ioo, Set.Ici]
  simp_all only [Set.setOf_subset_setOf, and_imp]
  intro a_1 a_2 a_3
  apply le_of_lt
  exact lt_of_le_of_lt h a_2
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

      -- simp_all [contDiff_id, ContDiff.prod, contDiff_const, ContDiff.add, ContDiff.mul] -- no work
      -- apply ContDiff.prod
      -- exact contDiff_const
      -- apply ContDiff.add
      -- exact contDiff_const
      -- apply ContDiff.mul
      -- apply ContDiff.sub
      -- exact contDiff_id
      -- exact contDiff_const
      -- exact contDiff_const --ja what is this

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

    -- unfold simple_boundary_function
    -- simp_rw [Set.eqOn_piecewise]
    -- simp_rw [Set.compl_Iio]
    -- rw [Ioo_inter_Ici_of_le]
    -- rw [Ioo_inter_Ici_of_le]
    -- nth_rw 1 [Ioo_inter_Ici_of_gt h22]
    -- -- rw [Ioo_inter_Ici_of_le]
    -- simp_rw [Set.Ioo_inter_Iio, Set.eqOn_refl]
    -- aesop

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

      -- apply ContDiff.prod <|> apply ContDiff.add <|> apply contDiff_const_sub <|> apply ContDiff.mul;
      -- try { exact contDiff_const <|> exact contDiff_id }

      -- simp only [contDiff_const_add, contDiff_const_sub, contDiff_const_mul, contDiff_const, contDiff_id]
      -- first|apply contDiff_const_sub|apply ContDiff.mul|skip
      -- repeat{first|exact contDiff_const|exact contDiff_id}
      -- repeat {
      --   apply contDiff_const_sub
      --   -- try apply contDiff_sub_const
      --   -- apply contDiff_const_mul
      -- }
      -- repeat {
      --   repeat{first|apply contDiff_const_sub|apply contDiff_sub_const|apply contDiff_const_mul}
      --   -- apply contDiff_sub_const
      --   repeat{first|exact contDiff_const|exact contDiff_id}
      -- }
      -- first|apply contDiff_const_sub|apply contDiff_sub_const|apply ContDiff.mul
      -- apply contDiff_const_mul
      -- apply contDiff_sub_const
      -- first|apply ContDiff.sub|apply ContDiff.mul|skip
      -- try simp only [contDiff_const, contDiff_id]
      -- first|apply ContDiff.sub|apply ContDiff.mul|skip
      -- try simp only [contDiff_const, contDiff_id]
      -- first|apply ContDiff.sub|apply ContDiff.mul|skip
      -- repeat {first|exact contDiff_const|exact contDiff_id}
      -- simp only [contDiff_const, ContDiff.sub]

      -- exact contDiff_const
      -- apply ContDiff.sub
      -- exact contDiff_const
      -- apply ContDiff.mul
      -- apply ContDiff.sub
      -- exact contDiff_id
      -- exact contDiff_const
      -- exact contDiff_const

    apply boundary_part_integrable R hct ff hcb (R.b + 1 + R.b - R.a) (R.b + 1 + R.b - R.a + 1) _ _ (hl := hl)
    apply ContDiff.continuous_deriv (n := 1) fcd (le_refl 1)
    apply ContDiff.differentiable (n := 1) fcd (le_refl 1)
    simp

    unfold simple_boundary_function
    simp_rw [Set.eqOn_piecewise]

    -- simp_rw [Set.Ioo, Set.compl_Iio, Set.Iio, Set.Ici, Set.inter_def]
    -- simp



    simp_rw [Set.compl_Iio]
    rw [Ioo_inter_Ici_of_le h3]
    rw [Ioo_inter_Ici_of_le h2]
    rw [Ioo_inter_Ici_of_le h1]
    simp_rw [Set.Ioo_inter_Iio, Set.eqOn_refl]
    aesop -- ok this is actually better at least to look at
    -- sorry
    -- all_goals have hhh : R.b + 1 + (R.b - R.a) ≤ R.b + 1 + R.b - R.a := by
    --   {rw [<- add_sub_assoc]}

    -- simp
    -- apply add_le_ -- nvm ig it doesn't want to add a number. this also hadn't even dealt with the main stuff yet

    -- rw [<- min_self (R.b + 1 + R.b - R.a + 1), <- Set.Ioo_inter_Iio (a := (R.b + 1 + R.b - R.a)) (b := (R.b + 1 + R.b - R.a + 1)) (c := (R.b + 1 + R.b - R.a + 1))]
    -- -- there has to be a better way to do this
    -- -- simp_rw [Set.inter_assoc, Set.inter_comm (Set.Iio (R.b + 1 + R.b - R.a + 1)), Set.inter_assoc, Set.inter_comm, Set.inter_compl_self (Set.Iio (R.b + 1 + R.b - R.a + 1)), Set.Iio_inter_Iio, Set.inter_assoc, Set.Iio_inter_Ioo]
    -- simp_rw [Set.Ioo_inter_Iio]
    -- simp_rw [Set.inter_assoc]
    -- repeat simp_rw [Set.inter_comm _ (Set.Iio _), <- Set.inter_assoc]
    -- simp
    -- aesop
    -- have : (R.b + 1 + R.b - R.a + 1) ⊓ R.b = R.b := by
    --   simp
    --   simp_rw [add_sub_assoc, add_assoc]
    --   simp
    --   nth_rw 2 [add_comm]
    --   simp_rw [<- add_assoc, <- add_sub_assoc]
    --   simp
    --   simp_rw [add_comm]
    --   apply le_add_of_le_of_nonneg
    --   apply le_of_lt
    --   exact R.a_lt_b
    --   simp
    -- rw [this]
    -- rw [Set.Ioo_eq_empty_of_le]
    -- simp
    -- have : R.b ≤ R.b + 1 + R.b - R.a := by
    --   apply le_of_lt
    --   simp_rw [add_sub_assoc, add_assoc]
    --   simp
    --   simp_rw [<- add_sub_assoc]
    --   simp
    --   simp_rw [add_comm]
    --   apply lt_add_of_lt_of_nonneg
    --   exact R.a_lt_b
    --   simp
    -- exact this

    -- rw [Set.Iio_inter_Ioo]
    -- have : (R.b + 1) ⊓ (R.b + 1 + R.b - R.a + 1) = R.b + 1 := by
    --   simp
    --   apply le_of_lt
    --   simp_rw [add_sub_assoc, add_assoc]
    --   simp
    --   simp_rw [<- add_sub_assoc]
    --   simp
    --   simp_rw [add_comm]
    --   apply lt_add_of_lt_of_nonneg
    --   exact R.a_lt_b
    --   simp
    -- rw [this]
    -- rw [Set.Ioo_eq_empty_of_le]
    -- simp
    -- apply le_of_lt
    -- rw [add_sub_assoc]
    -- simp
    -- exact R.a_lt_b

    -- rw [Set.Iio_inter_Ioo]
    -- simp

    -- exact fun ⦃x⦄ ↦ congrFun rfl

  done

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
    · sorry
    · intro x
      -- nah i basically have to work out how to take projection into the deriv
      -- maybe i actually just have to define that that's how deriv works in this case?
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
