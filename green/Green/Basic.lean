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

-- don't actually need this? just the separate parts since it's constructivist in green's anyway atm, tho good isolated test (also idk if trans works backwards)
theorem simple_boundary_path_proj_fst_Integrable (hct : Continuous R.f_t) (hcb : Continuous R.f_b) {hl : Continuous L} {hrb : Continuous (deriv fun x ↦ (x, R.f_b x))} {hrb2 : Differentiable ℝ fun x ↦ (x, R.f_b x)} : pathIntegral_proj_fst_Integrable R.a (R.b+1+R.b-R.a+1) L (simple_boundary_function R) := by
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
    apply boundary_part_integrable R hct ff hcb R.a R.b R.a_lt_b _ (hl := hl) (hrb := hrb) (hrb2 := hrb2)

    unfold simple_boundary_function
    simp_rw [Set.eqOn_piecewise]
    rw [<- min_self R.b, <- Set.Ioo_inter_Iio (a := R.a) (b := R.b) (c := R.b), min_self]
    simp_rw [Set.inter_assoc _ (Set.Iio R.b), Set.inter_compl_self (Set.Iio R.b)]
    -- mostly aesop
    simp_all only [differentiable_id', Set.inter_self, Set.inter_empty, Set.empty_inter, Set.eqOn_empty, Set.compl_Iio, and_self, and_true]
    exact fun ⦃x⦄ ↦ congrFun rfl

 -- todo: maybe write a custom tactic for this intersection nonsense?
  · let ff : ℝ → ℝ×ℝ := fun r ↦ (R.b, R.f_b R.b + (r - R.b) * (R.f_t R.b - R.f_b R.b))
    apply boundary_part_integrable R hct ff hcb R.b (R.b + 1) _ _ (hl := hl)
    sorry
    sorry
    exact lt_add_one R.b

    unfold simple_boundary_function
    simp_rw [Set.eqOn_piecewise]
    rw [<- min_self (R.b + 1), <- Set.Ioo_inter_Iio (a := R.b) (b := R.b + 1) (c := R.b + 1), min_self]
    simp_rw [Set.inter_assoc _ (Set.Iio (R.b + 1)), Set.inter_comm (Set.Iio (R.b + 1)), Set.inter_assoc _ _ (Set.Iio (R.b + 1))ᶜ, Set.inter_compl_self (Set.Iio (R.b + 1)), Set.Iio_inter_Iio, Set.Ioo_inter_Iio]
    simp
    exact fun ⦃x⦄ ↦ congrFun rfl

  · let ff : ℝ → ℝ×ℝ := fun r ↦ (R.b + 1 + R.b - r, R.f_t (R.b + 1 + R.b - r))
    apply boundary_part_integrable R hct ff hcb (R.b + 1) (R.b + 1 + R.b - R.a) _ _ (hl := hl)
    sorry
    sorry
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
    aesop
    -- there has to be a better way to do this
    simp_rw [Set.inter_assoc _ (Set.Iio (R.b + 1 + R.b - R.a)), Set.inter_comm (Set.Iio (R.b + 1 + R.b - R.a)), Set.inter_assoc _ _ (Set.Iio (R.b + 1 + R.b - R.a))ᶜ, Set.inter_compl_self (Set.Iio (R.b + 1 + R.b - R.a)), Set.Iio_inter_Iio, Set.Ioo_inter_Iio]
    simp
    exact fun ⦃x⦄ ↦ congrFun rfl

  repeat sorry
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
theorem green_split_alpha (s_1 s_2 s_3 : ℝ) (hi0 : pathIntegral_proj_fst_Integrable 0 s_1 L k) (hi1 : pathIntegral_proj_fst_Integrable s_1 s_2 L k) (hi2 : pathIntegral_proj_fst_Integrable s_2 s_3 L k) (hi3 : pathIntegral_proj_fst_Integrable s_3 1 L k) (hs01 : pathIntegral_proj_fst 0 s_1 L k = ∫ x in a..b, L (x,f x)) (hs12 : pathIntegral_proj_fst s_1 s_2 L k = 0) (hs23 : pathIntegral_proj_fst s_2 s_3 L k = ∫ x in b..a, L (x,g x)) (hs30 : pathIntegral_proj_fst s_3 1 L k = 0): pathIntegral_proj_fst 0 1 L k = (∫ x in a..b, L (x,f x)) - ∫ x in a..b, L (x,g x) := by
  have hi20 : pathIntegral_proj_fst_Integrable s_2 1 L k := by
    apply pathIntegral_proj_fst_Integrable_trans hi2 hi3
  have hi10 : pathIntegral_proj_fst_Integrable s_1 1 L k := by
    apply pathIntegral_proj_fst_Integrable_trans hi1 hi20
  rw [<- pathIntegral_proj_fst_split_at s_1]
  nth_rw 2 [<- pathIntegral_proj_fst_split_at s_2]
  nth_rw 3 [<- pathIntegral_proj_fst_split_at s_3]
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
