import Carleson.ForestOperator.LargeSeparation
import Carleson.ForestOperator.RemainingTiles
import Carleson.ToMathlib.MeasureTheory.Integral.SetIntegral
import Carleson.ToMathlib.Order.Chain

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Lemmas 7.4.4 -/

/-- The constant used in `correlation_separated_trees`.
Has value `2 ^ (550 * a ^ 3 - 3 * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_4 (a n : ℕ) : ℝ≥0 := 2 ^ (550 * (a : ℝ) ^ 3 - 3 * n)

lemma correlation_separated_trees_of_subset (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂) g₂ x)‖₊ ≤
    C7_4_4 a n *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

/-- Lemma 7.4.4. -/
lemma correlation_separated_trees (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂) g₂ x)‖₊ ≤
    C7_4_4 a n *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

/-! ## Section 7.7 -/

def rowDecomp_zornset (s : Set (𝔓 X)) :=
  { x : Set (𝔓 X) | x ⊆ s} ∩ {x : Set (𝔓 X) | x.PairwiseDisjoint (𝓘 ·: _ → Set X)} ∩
    {x : Set (𝔓 X) | x ⊆ {u | Maximal (· ∈ 𝓘 '' s) (𝓘 u)}}

lemma mem_rowDecomp_zornset_iff (s s' : Set (𝔓 X)) :
    s' ∈ rowDecomp_zornset s ↔ (s' ⊆ s ∧ s'.PairwiseDisjoint (𝓘 ·: _ → Set X) ∧
      ∀ u ∈ s', Maximal (· ∈ 𝓘 '' s) (𝓘 u)) := by
  rw [rowDecomp_zornset,mem_inter_iff,mem_inter_iff,mem_setOf,mem_setOf,mem_setOf,and_assoc]
  nth_rw 2 [subset_def]
  simp_rw [mem_setOf]

lemma rowDecomp_zornset_chain_Union_bound (s' : Set (𝔓 X)) {c : Set (Set (𝔓 X))} (hc : c ⊆ rowDecomp_zornset s')
    (hc_chain : IsChain (· ⊆ ·) c) :
    (⋃ s ∈ c,s) ∈ rowDecomp_zornset s' ∧ ∀ s ∈ c, s ⊆ ⋃ s'' ∈ c, s'' := by
  simp_rw [rowDecomp_zornset,subset_inter_iff] at hc ⊢
  obtain ⟨⟨hc₁,hc₂⟩,hc₃⟩ := hc
  simp_rw [mem_inter_iff,mem_setOf]
  repeat constructor
  · exact iUnion₂_subset_iff.mpr hc₁
  · exact hc_chain.pairwiseDisjoint_iUnion₂ _ _ hc₂
  · exact iUnion₂_subset_iff.mpr hc₃
  · exact fun s a_1 ↦ subset_iUnion₂_of_subset s a_1 fun ⦃a_2⦄ a ↦ a

def rowDecomp_𝔘 (t : Forest X n) (j : ℕ) : Set (𝔓 X) :=
  (zorn_subset (rowDecomp_zornset (t \ ⋃ i < j, rowDecomp_𝔘 t i))
  (fun _ hc => Exists.intro _ ∘ rowDecomp_zornset_chain_Union_bound _ hc)).choose

lemma rowDecomp_𝔘_def (t : Forest X n) (j : ℕ) :
    Maximal (fun x ↦ x ∈ rowDecomp_zornset (t \ ⋃ i < j, rowDecomp_𝔘 t i)) (rowDecomp_𝔘 t j) := by
  rw [rowDecomp_𝔘]
  apply Exists.choose_spec

lemma rowDecomp_𝔘_mem_zornset (t : Forest X n) (j : ℕ) :
    t.rowDecomp_𝔘 j ∈ rowDecomp_zornset (t \ ⋃ i < j, rowDecomp_𝔘 t i) :=
  (rowDecomp_𝔘_def t j).prop

lemma rowDecomp_𝔘_subset (t : Forest X n) (j : ℕ) :
    t.rowDecomp_𝔘 j ⊆ t \ ⋃ i < j, rowDecomp_𝔘 t i := by
  have := rowDecomp_𝔘_mem_zornset t j
  rw [mem_rowDecomp_zornset_iff] at this
  exact this.left

lemma rowDecomp_𝔘_pairwiseDisjoint (t : Forest X n) (j : ℕ) :
    (t.rowDecomp_𝔘 j).PairwiseDisjoint (𝓘 ·: _ → Set X) := by
  have := rowDecomp_𝔘_mem_zornset t j
  rw [mem_rowDecomp_zornset_iff] at this
  exact this.right.left

lemma mem_rowDecomp_𝔘_maximal (t : Forest X n) (j : ℕ) :
    ∀ x ∈ (t.rowDecomp_𝔘 j), Maximal (· ∈ 𝓘 '' (t \ ⋃ i < j, rowDecomp_𝔘 t i)) (𝓘 x) := by
  have := rowDecomp_𝔘_mem_zornset t j
  rw [mem_rowDecomp_zornset_iff] at this
  exact this.right.right

lemma rowDecomp_𝔘_subset_forest (t : Forest X n) (j : ℕ) :
  rowDecomp_𝔘 t j ⊆ t := subset_trans (rowDecomp_𝔘_subset t j) diff_subset

/-- The row-decomposition of a tree, defined in the proof of Lemma 7.7.1.
The indexing is off-by-one compared to the blueprint. -/
def rowDecomp (t : Forest X n) (j : ℕ) : Row X n where
  𝔘 := rowDecomp_𝔘 t j
  𝔗 := t
  nonempty' hu := t.nonempty (rowDecomp_𝔘_subset_forest t j hu)
  ordConnected' hu:= t.ordConnected' (rowDecomp_𝔘_subset_forest t j hu)
  𝓘_ne_𝓘' hu := t.𝓘_ne_𝓘' (rowDecomp_𝔘_subset_forest t j hu)
  smul_four_le' hu := t.smul_four_le' (rowDecomp_𝔘_subset_forest t j hu)
  stackSize_le' := le_trans
    (stackSize_mono (rowDecomp_𝔘_subset_forest t j))
    t.stackSize_le'
  dens₁_𝔗_le' hu := t.dens₁_𝔗_le' (rowDecomp_𝔘_subset_forest t j hu)
  lt_dist' hu hu' := t.lt_dist' (rowDecomp_𝔘_subset_forest t j hu) (rowDecomp_𝔘_subset_forest t j hu')
  ball_subset' hu := t.ball_subset' (rowDecomp_𝔘_subset_forest t j hu)
  pairwiseDisjoint' := rowDecomp_𝔘_pairwiseDisjoint t j

lemma mem_forest_of_mem {t: Forest X n} {j : ℕ} {x : 𝔓 X} (hx : x ∈ t.rowDecomp j) : x ∈ t :=
  rowDecomp_𝔘_subset_forest t j hx

lemma rowDecomp_𝔘_eq (t : Forest X n) (j : ℕ) :
  (t.rowDecomp j).𝔘 = rowDecomp_𝔘 t j := rfl

lemma mem_rowDecomp_iff_mem_rowDecomp_𝔘 (t : Forest X n) (j : ℕ) : ∀ x,
  x ∈ t.rowDecomp j ↔ x ∈ t.rowDecomp_𝔘 j := by intros; rfl

lemma stackSize_remainder_ge_one_of_exists (t : Forest X n) (j : ℕ) (x:X)
    (this : ∃ 𝔲' ∈ (t.rowDecomp j).𝔘, x ∈ 𝓘 𝔲') :
    1 ≤ stackSize ((t \ ⋃ i < j, t.rowDecomp i) ∩ t.rowDecomp j: Set _) x := by
  obtain ⟨𝔲',h𝔲'⟩ := this
  dsimp [stackSize]
  rw [← Finset.sum_erase_add _ (a := 𝔲')]
  · rw [indicator_apply,← Grid.mem_def,if_pos h𝔲'.right,Pi.one_apply]
    simp only [le_add_iff_nonneg_left, zero_le]
  simp only [mem_inter_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨t.rowDecomp_𝔘_subset j h𝔲'.left,h𝔲'.left⟩

lemma remainder_stackSize_le (t : Forest X n) (j : ℕ) :
  ∀ x:X, stackSize (t \ ⋃ i < j, t.rowDecomp i : Set _) x ≤ 2 ^ n - j := by
    intro x
    induction j with
    | zero =>
      simp only [not_lt_zero', iUnion_of_empty, iUnion_empty, diff_empty, tsub_zero]
      exact t.stackSize_le'
    | succ j hinduct =>
      if h: ∃ 𝔲 ∈ (t \ ⋃ i < j + 1, t.rowDecomp i : Set _), x ∈ 𝓘 𝔲 then
        have : ∃ s, Maximal (· ∈ (𝓘 '' (t \ ⋃ i < j, t.rowDecomp i : Set _))) s ∧ x ∈ s := by
          obtain ⟨𝔲,h𝔲⟩ := h
          rw [biUnion_lt_succ,← diff_diff,mem_diff] at h𝔲
          exact (((toFinite _).image 𝓘).exists_le_maximal ⟨𝔲,h𝔲.left.left,rfl⟩).imp
            fun _ hz => ⟨hz.right, Grid.mem_mono hz.left h𝔲.right⟩
        obtain ⟨𝔲,h𝔲⟩ := h
        simp only [biUnion_lt_succ, ← diff_diff] at h𝔲 ⊢
        rw [stackSize_sdiff_eq,← Nat.sub_sub]
        apply tsub_le_tsub hinduct (stackSize_remainder_ge_one_of_exists t j x _)
        rw [mem_diff] at h𝔲
        apply (or_not).elim id
        push_neg
        intro h
        apply this.elim
        intro _ ⟨hmax,hz⟩
        obtain ⟨u,hu,rfl⟩ := hmax.prop
        use u
        rw [mem_𝔘]
        refine ⟨?_,hz⟩
        apply (t.rowDecomp_𝔘_def j).mem_of_prop_insert
        rw [mem_rowDecomp_zornset_iff]
        simp only [mem_insert_iff, mem_diff,
          mem_𝔘, mem_iUnion, not_and, forall_eq_or_imp]
        constructor
        · rw [insert_subset_iff]
          simp_rw [rowDecomp_𝔘_eq] at hu
          exact ⟨hu, rowDecomp_𝔘_subset _ _⟩
        constructor
        · rw [pairwiseDisjoint_insert]
          use t.rowDecomp_𝔘_pairwiseDisjoint j
          intro k hk hne
          have : 𝓘 u = 𝓘 k → u = k := by
            specialize h k hk
            intro heq
            rw [← heq] at h
            contradiction
          obtain (h|h|h) := le_or_ge_or_disjoint (i := 𝓘 u) (j := 𝓘 k)
          case inr.inr => exact h
          · have heq : 𝓘 u = 𝓘 k := by
              apply le_antisymm h
              exact hmax.le_of_ge ⟨k,rowDecomp_𝔘_subset t j hk,rfl⟩ h
            exact (hne (this heq)).elim
          · have heq : 𝓘 u = 𝓘 k := by
              apply le_antisymm _ h
              exact (mem_rowDecomp_𝔘_maximal t j k hk).le_of_ge ⟨u,hu,rfl⟩ h
            exact (hne (this heq)).elim
        · exact ⟨hmax, mem_rowDecomp_𝔘_maximal t j⟩
      else
        dsimp [stackSize]
        push_neg at h
        rw [Finset.sum_congr rfl (g := fun _ => 0) (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, indicator_apply_eq_zero,
            Pi.one_apply, one_ne_zero] at h ⊢
          exact h)]
        rw [Finset.sum_eq_zero (fun _ _ => rfl)]
        exact zero_le _

/-- Part of Lemma 7.7.1 -/
@[simp]
lemma biUnion_rowDecomp : ⋃ j < 2 ^ n, t.rowDecomp j = (t : Set (𝔓 X)) := by
  apply subset_antisymm
  · simp_rw [iUnion_subset_iff,rowDecomp_𝔘_eq]
    exact fun i _ => rowDecomp_𝔘_subset_forest t i
  · rw [← diff_eq_empty]
    exact eq_empty_of_forall_stackSize_zero _ fun x =>
      Nat.eq_zero_of_le_zero ((Nat.sub_self _).symm ▸ remainder_stackSize_le t (2 ^ n) x)

/-- Part of Lemma 7.7.1 -/
lemma pairwiseDisjoint_rowDecomp :
    (Iio (2 ^ n)).PairwiseDisjoint (rowDecomp t · : ℕ → Set (𝔓 X)) := by
  intro i hi j hj hne
  rw [onFun_apply,Set.disjoint_iff]
  wlog hij : i < j
  · rw [Set.inter_comm]
    apply this hj hi hne.symm
    omega
  intro x hx
  obtain ⟨hx₁,hx₂⟩ := hx
  revert hx₁
  simp only [mem_𝔘, mem_empty_iff_false, imp_false]
  rw [rowDecomp_𝔘_eq t j] at hx₂
  have := ((rowDecomp_𝔘_subset t j) hx₂).right
  simp_rw [mem_iUnion, exists_prop, not_exists, not_and] at this
  exact this i hij

@[simp] lemma rowDecomp_apply : t.rowDecomp j u = t u := rfl

/-- The constant used in `row_bound`.
Has value `2 ^ (156 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_1 (a n : ℕ) : ℝ≥0 := (C7_3_1_1 a : ℝ≥0) * 2 ^ (a ^ 3 - n/2:ℝ)

lemma C7_7_2_1_bounds (a n : ℕ) (ha : 2 ≤ a) : (C7_3_1_1 a : ℝ≥0∞) * 2 ^ ((4 * a + 1-n)/2 : ℝ) ≤ C7_7_2_1 a n := by
  rw [C7_7_2_1_def,ENNReal.coe_mul]
  gcongr
  rw [ENNReal.coe_rpow_of_ne_zero (by norm_num),ENNReal.coe_ofNat]
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [sub_div, add_div, mul_div_right_comm]
  norm_num
  have : 2 ≤ (a:ℝ) := by
    simp only [Nat.ofNat_le_cast]
    exact ha
  calc (2:ℝ) * a + 1/2
  _ ≤ 2 * a + 2 * 2 := by
    gcongr
    norm_num
  _ ≤ 2 * a + 2 * a := by gcongr
  _ ≤ (a:ℝ) ^ 3 := by
    rw [← left_distrib,← two_mul, pow_three]
    gcongr

/-- The constant used in `indicator_row_bound`.
Has value `2 ^ (257 * a ^ 3 - n / 2)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_2_2 (a n : ℕ) : ℝ≥0 := (C7_3_1_2 a : ℝ≥0) * 2 ^ (a ^ 3 - n/2:ℝ)

lemma C7_7_2_2_bounds (a n : ℕ) (ha : 2 ≤ a) : (C7_3_1_2 a : ℝ≥0∞) * 2 ^ ((4 * a + 1-n)/2 : ℝ) ≤ C7_7_2_2 a n := by
  rw [C7_7_2_2_def,ENNReal.coe_mul]
  gcongr
  rw [ENNReal.coe_rpow_of_ne_zero (by norm_num),ENNReal.coe_ofNat]
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [sub_div, add_div, mul_div_right_comm]
  norm_num
  have : 2 ≤ (a:ℝ) := by
    simp only [Nat.ofNat_le_cast]
    exact ha
  calc (2:ℝ) * a + 1/2
  _ ≤ 2 * a + 2 * 2 := by
    gcongr
    norm_num
  _ ≤ 2 * a + 2 * a := by gcongr
  _ ≤ (a:ℝ) ^ 3 := by
    rw [← left_distrib,← two_mul, pow_three]
    gcongr

-- move
lemma _root_.ENNReal.sq_le_mul_right {a : ℝ≥0∞} (htop : a ≠ ⊤) (b : ℝ≥0∞) : a ^ 2 ≤ b * a ↔ a ≤ b := by
  if hzero : (a = 0) then
    subst hzero
    simp
  else
    rw [pow_two]
    exact ENNReal.mul_le_mul_right hzero htop

-- move
lemma _root_.ENNReal.le_of_pow_le_pow {a b : ℝ≥0∞} {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n → a ≤ b := by
  contrapose!
  exact (ENNReal.pow_right_strictMono hn ·)

lemma _root_.ENNReal.le_of_rpow_le_rpow {a b : ℝ≥0∞} {r : ℝ} (hr : 0 < r) : a ^ r ≤ b ^ r → a ≤ b := by
  rw [ENNReal.rpow_le_rpow_iff hr]
  exact id

-- move to mathlib
omit [TileStructure Q D κ S o] in
lemma sq_eLpNorm_eq (hg : BoundedCompactSupport g) :
    (eLpNorm (g) 2 volume) ^ 2 =
      ‖∫ (x:X), conj (g x) * g x‖₊ := by
  simp only [conj_mul', ← ofReal_pow, integral_complex_ofReal, nnnorm_real, ←
    enorm_eq_nnnorm]
  rw [(hg.memLp 2).eLpNorm_eq_integral_rpow_norm (by positivity) (by norm_num)]
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two]
  rw [Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  nth_rw 2 [← Nat.cast_ofNat (n := 2)]
  rw [Real.rpow_inv_natCast_pow (n := 2) (by positivity) (by positivity)]

-- move to mathlib
@[to_additive]
lemma _root_.MonoidHomClass.map_mulIndicator {F X A B: Type*} [Monoid A] [Monoid B] [FunLike F A B] [MonoidHomClass F A B]
  {s : Set X} (f : F) (x : X) (g : X → A) : f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x := by
  exact (MonoidHomClass.toMonoidHom f).map_mulIndicator s g x

lemma refined_density_tree_bound1 (hu : u ∈ t) (hf : BoundedCompactSupport f):
    eLpNorm (G.indicator <| carlesonSum (t u) f) 2 volume ≤
      C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  have hf_indicator : BoundedCompactSupport (G.indicator (carlesonSum (t u) f)) :=
    BoundedCompactSupport.indicator_of_isBounded_range hf.carlesonSum.isBounded
      hf.carlesonSum.stronglyMeasurable isBounded_G measurableSet_G
  rw [← ENNReal.sq_le_mul_right (hf_indicator.memLp 2).eLpNorm_ne_top, sq_eLpNorm_eq hf_indicator]
  simp_rw [AddMonoidHomClass.map_indicator, ← indicator_mul]
  eta_expand
  simp_rw [indicator_mul_left,← AddMonoidHomClass.map_indicator]
  exact density_tree_bound1' hf hf_indicator (support_indicator_subset) hu

lemma adjoint_density_tree_bound1'
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g)
    (hg2 : g.support ⊆ G) (hu : u ∈ t) :
    ‖∫ x, conj (adjointCarlesonSum (t u) g x) * f x‖₊ ≤
    C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  simp_rw [← adjointCarlesonSum_adjoint hf hg]
  exact density_tree_bound1' hf hg hg2 hu

lemma adjoint_refined_density_tree_bound1 (hu : u ∈ t) (hf : BoundedCompactSupport f) (hf2 : f.support ⊆ G):
    eLpNorm (adjointCarlesonSum (t u) f) 2 volume ≤
      C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  have hf_indicator : BoundedCompactSupport ((adjointCarlesonSum (t u) f)) :=
    hf.adjointCarlesonSum
  rw [← ENNReal.sq_le_mul_right (hf_indicator.memLp 2).eLpNorm_ne_top, sq_eLpNorm_eq hf_indicator]
  trans
  · exact adjoint_density_tree_bound1' (X := X) hf_indicator (hf) hf2 hu
  apply Eq.le
  ring_nf

-- move somewhere else
lemma _root_.Bornology.IsBounded.range_one {α : Type*} [Nonempty α] :
    Bornology.IsBounded (range (1 : α → ℂ)) := by
  rw [Set.range_one]
  exact isBounded_singleton

lemma refined_density_tree_bound2 (hu : u ∈ t) (hf : BoundedCompactSupport f) :
    eLpNorm (G.indicator <| carlesonSum (t u) (F.indicator f)) 2 volume ≤
      ↑(C7_3_1_2 a) * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm (F.indicator f) 2 volume := by
  have hind: BoundedCompactSupport (F.indicator f) :=
    BoundedCompactSupport.indicator_of_isBounded_range hf.isBounded
      hf.stronglyMeasurable isBounded_F measurableSet_F
  have hf_indicator : BoundedCompactSupport (G.indicator (carlesonSum (t u) (F.indicator f))) :=
    BoundedCompactSupport.indicator_of_isBounded_range hind.carlesonSum.isBounded
      hind.carlesonSum.stronglyMeasurable isBounded_G measurableSet_G
  rw [← ENNReal.sq_le_mul_right (hf_indicator.memLp 2).eLpNorm_ne_top, sq_eLpNorm_eq hf_indicator]
  simp_rw [AddMonoidHomClass.map_indicator, ← indicator_mul]
  eta_expand
  simp_rw [indicator_mul_left,← AddMonoidHomClass.map_indicator]
  exact density_tree_bound2' hind support_indicator_subset hf_indicator support_indicator_subset hu

lemma adjoint_density_tree_bound2'
    (hf : BoundedCompactSupport f)
    (h2f : support f ⊆ F)
    (hg : BoundedCompactSupport g)
    (h2g : support g ⊆ G)
    (hu : u ∈ t) :
    ‖∫ x, conj (adjointCarlesonSum (t u) g x) * f x‖₊ ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  simp_rw [← adjointCarlesonSum_adjoint hf hg]
  exact density_tree_bound2' hf h2f hg h2g hu

lemma adjoint_refined_density_tree_bound2 (hu : u ∈ t) (hf : BoundedCompactSupport f) (h2f : f.support ⊆ G):
    eLpNorm (F.indicator <| adjointCarlesonSum (t u) f) 2 volume ≤
      ↑(C7_3_1_2 a) * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm (f) 2 volume := by
  have hind: BoundedCompactSupport (f) := hf
  have hf_indicator : BoundedCompactSupport (F.indicator (adjointCarlesonSum (t u) (f))) :=
    hind.adjointCarlesonSum.indicator measurableSet_F
  rw [← ENNReal.sq_le_mul_right (hf_indicator.memLp 2).eLpNorm_ne_top, sq_eLpNorm_eq hf_indicator]
  simp_rw [AddMonoidHomClass.map_indicator, ← indicator_mul]
  eta_expand
  simp_rw [indicator_mul_right]
  trans
  · exact adjoint_density_tree_bound2' hf_indicator support_indicator_subset hind h2f hu
  · apply Eq.le
    ring_nf




lemma C7_7_2_bound1 (hu : u ∈ t) (hf : BoundedCompactSupport f):
    eLpNorm (G.indicator <| carlesonSum (t u) f) 2 volume ≤
      C7_7_2_1 a n * eLpNorm f 2 volume := by
  calc eLpNorm (G.indicator <| carlesonSum (t u) f) 2 volume
  _ ≤ C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
    exact refined_density_tree_bound1 hu hf
  _ ≤ C7_3_1_1 a * 2 ^ ((4 * a + 1 - n) / 2 : ℝ) * eLpNorm f 2 volume := by
    rw [div_eq_mul_inv _ (2:ℝ),ENNReal.rpow_mul]
    gcongr
    rw [add_sub_right_comm]
    exact t.dens₁_𝔗_le hu
  _ ≤ C7_7_2_1 a n * eLpNorm f 2 volume := by
    gcongr
    exact C7_7_2_1_bounds a n ((show 2 ≤ 4 from by norm_num).trans (PreProofData.four_le_a X))


lemma adjoint_C7_7_2_bound1 (hu : u ∈ t) (hf : BoundedCompactSupport f):
    eLpNorm (adjointCarlesonSum (t u) (G.indicator f)) 2 volume ≤
      C7_7_2_1 a n * eLpNorm f 2 volume := by
  calc eLpNorm (adjointCarlesonSum (t u) (G.indicator f)) 2 volume
  _ ≤ C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm (G.indicator f) 2 volume := by
    exact adjoint_refined_density_tree_bound1 hu (hf.indicator measurableSet_G)
      support_indicator_subset
  _ ≤ C7_3_1_1 a * 2 ^ ((4 * a + 1 - n) / 2 : ℝ) * eLpNorm f 2 volume := by
    rw [div_eq_mul_inv _ (2:ℝ),ENNReal.rpow_mul]
    gcongr
    · rw [add_sub_right_comm]
      exact t.dens₁_𝔗_le hu
    · exact eLpNorm_indicator_le f
  _ ≤ C7_7_2_1 a n * eLpNorm f 2 volume := by
    gcongr
    exact C7_7_2_1_bounds a n ((show 2 ≤ 4 from by norm_num).trans (PreProofData.four_le_a X))


lemma C7_7_2_bound2 (hu : u ∈ t) (hf : BoundedCompactSupport f):
    eLpNorm (G.indicator <| carlesonSum (t u) (F.indicator f)) 2 volume ≤
      C7_7_2_2 a n * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  calc eLpNorm (G.indicator <| carlesonSum (t u) (F.indicator f)) 2 volume
  _ ≤ C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm (F.indicator f) 2 volume := by
    exact refined_density_tree_bound2 hu hf
  _ ≤ C7_3_1_2 a * 2 ^ ((4 * a + 1 - n) / 2 : ℝ) * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
    rw [div_eq_mul_inv _ (2:ℝ),ENNReal.rpow_mul]
    gcongr
    · rw [add_sub_right_comm]
      exact t.dens₁_𝔗_le hu
    · apply eLpNorm_mono
      intro x
      rw [Set.indicator_apply, apply_ite (‖·‖)]
      split <;> simp
  _ ≤ C7_7_2_2 a n * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
    gcongr
    -- it suffices that 2 ≤ a. this can be improved, but involves solving a cubic inequality.
    -- 1 is not enough
    exact C7_7_2_2_bounds a n ((show 2 ≤ 4 from by norm_num).trans (PreProofData.four_le_a X))


lemma adjoint_C7_7_2_bound2 (hu : u ∈ t) (hf : BoundedCompactSupport f):
    eLpNorm (F.indicator <| adjointCarlesonSum (t u) (G.indicator f)) 2 volume ≤
      C7_7_2_2 a n * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  calc eLpNorm (F.indicator <| adjointCarlesonSum (t u) (G.indicator f)) 2 volume
  _ ≤ C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm (G.indicator f) 2 volume := by
    exact adjoint_refined_density_tree_bound2 hu (hf.indicator measurableSet_G)
      support_indicator_subset
  _ ≤ C7_3_1_2 a * 2 ^ ((4 * a + 1 - n) / 2 : ℝ) * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
    rw [div_eq_mul_inv _ (2:ℝ),ENNReal.rpow_mul]
    gcongr
    · rw [add_sub_right_comm]
      exact t.dens₁_𝔗_le hu
    · exact eLpNorm_indicator_le f
  _ ≤ C7_7_2_2 a n * dens₂ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
    gcongr
    -- it suffices that 2 ≤ a. this can be improved, but involves solving a cubic inequality.
    -- 1 is not enough
    exact C7_7_2_2_bounds a n ((show 2 ≤ 4 from by norm_num).trans (PreProofData.four_le_a X))

-- move to Carleson/TileStructure
lemma coeGrid_isBounded {i : Grid X} : IsBounded (i : Set X) := by
  rw [isBounded_iff_subset_ball (c i)]
  use 4 * D ^ (s i), Grid_subset_ball

lemma part_1 (j : ℕ) {A:Set X}:
    (eLpNorm (A.indicator <| ∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) g) 2 volume) ^ 2
    = (eLpNorm (A.indicator <| ∑ u ∈ {p | p ∈ rowDecomp t j},
      ∑ p ∈ {p | p ∈ t.𝔗 u}, ((𝓘 u: Set X).indicator <|
        adjointCarleson p ((𝓘 u:Set X).indicator g))) 2 volume) ^ 2 := by
  congr
  apply congrArg A.indicator
  apply Finset.sum_congr rfl
  intro u hu'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu'
  ext x
  rw [adjointCarlesonSum,Finset.sum_apply]
  apply Finset.sum_congr (by ext; simp)
  intro p hp
  simp only [defaultA, defaultD.eq_1, defaultκ.eq_1, mem_𝔗, Finset.mem_filter, Finset.mem_univ,
    true_and] at hp
  rw [adjoint_tile_support2 (mem_forest_of_mem hu') hp]


lemma part_2 (hg : BoundedCompactSupport g) {A : Set X} (hA : MeasurableSet A) (j : ℕ):
    (eLpNorm (A.indicator <| ∑ u ∈ {p | p ∈ rowDecomp t j},
      ∑ p ∈ {p | p ∈ t.𝔗 u}, ((𝓘 u: Set X).indicator <|
        adjointCarleson p ((𝓘 u:Set X).indicator g))) 2 volume) ^ 2
    = ∑ u ∈ {p | p ∈ rowDecomp t j}, .ofReal (∫ x in (𝓘 u : Set X),
     ‖ (A.indicator (adjointCarlesonSum (t u) ((𝓘 u : Set X).indicator g)) x)‖ ^ 2) := by
  simp_rw [Finset.indicator_sum _ A]
  calc (eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j},
      ∑ p ∈ {p | p ∈ t.𝔗 u}, A.indicator (((𝓘 u: Set X).indicator (
        adjointCarleson p ((𝓘 u:Set X).indicator g))))) 2 volume) ^ 2
    = ENNReal.ofReal ( ∫ (x : X), ‖ ∑ u ∈ {p | p ∈ rowDecomp t j},
      ∑ p ∈ {p | p ∈ t.𝔗 u}, A.indicator (((𝓘 u: Set X).indicator <|
        adjointCarleson p ((𝓘 u:Set X).indicator g))) x‖ ^ 2) := by

        rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by finiteness) ?memLp]
        case memLp =>
          apply MeasureTheory.memLp_finset_sum'
          intro u hu
          apply MeasureTheory.memLp_finset_sum'
          intro p hp
          refine MemLp.indicator hA (MemLp.indicator coeGrid_measurable ?_)
          exact hg.indicator coeGrid_measurable |>.adjointCarleson (X := X) (p := p) |>.memLp 2
        rw [← ENNReal.ofReal_pow (by positivity),ENNReal.toReal_ofNat]
        rw [← Real.rpow_two,← Real.rpow_mul (by positivity), inv_mul_cancel₀ (by norm_num),
          Real.rpow_one]
        simp_rw [Finset.sum_apply,Real.rpow_two]
  _ = ENNReal.ofReal ( ∫ (x : X), ‖ ∑ u ∈ {p | p ∈ rowDecomp t j},
      (𝓘 u: Set X).indicator (A.indicator <| ∑ p ∈ {p | p ∈ t.𝔗 u}, (
        adjointCarleson p ((𝓘 u:Set X).indicator g))) x‖ ^ 2) := by
      simp_rw [Finset.indicator_sum, Set.indicator_indicator, Set.inter_comm A, Finset.sum_apply]
  _ = ENNReal.ofReal ( ∫ (x : X), ‖ ∑ u ∈ {p | p ∈ rowDecomp t j},
      (𝓘 u: Set X).indicator (A.indicator <|
        adjointCarlesonSum (t u) ((𝓘 u:Set X).indicator g)) x‖ ^ 2) := by
    eta_expand -- otherwise can't rewrite with `adjointCarlesonSum`
    simp_rw [adjointCarlesonSum, Finset.sum_apply]
  _ = ENNReal.ofReal ( ∫ (x : X), ∑ u ∈ {p | p ∈ rowDecomp t j},
      ‖ (𝓘 u: Set X).indicator (A.indicator <|
        adjointCarlesonSum (t u) ((𝓘 u:Set X).indicator g)) x‖ ^ 2) := by
      congr
      ext x
      if h : x ∈ ⋃ u ∈ {p | p ∈ rowDecomp t j}, (𝓘 u:Set X) then
        simp only [mem_setOf_eq, mem_iUnion, exists_prop] at h
        obtain ⟨u,hu,hx⟩ := h
        rw [Finset.sum_eq_single_of_mem u,Finset.sum_eq_single_of_mem
          (s := Finset.filter (fun p ↦ p ∈ t.rowDecomp j) Finset.univ) u] <;>
            simp [Finset.mem_filter, Finset.mem_univ, true_and] <;> try assumption
        all_goals
          intro b hb hne hx'
          rw [mem_rowDecomp_iff_mem_rowDecomp_𝔘] at hu hb
          exact (hne ((rowDecomp_𝔘_pairwiseDisjoint t j).elim_set hb hu x hx' hx)).elim
      else
        simp only [mem_setOf_eq, mem_iUnion, exists_prop, not_exists, not_and] at h
        rw [Finset.sum_eq_zero,Finset.sum_eq_zero,norm_zero,zero_pow (by norm_num)]
        · intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          rw [pow_eq_zero_iff (by norm_num),norm_eq_zero]
          apply Set.indicator_of_not_mem (h u hu)
        · intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          apply Set.indicator_of_not_mem (h u hu)
  _ = ∑ u ∈ {p | p ∈ rowDecomp t j},ENNReal.ofReal (∫ (x : X),
      ‖ (𝓘 u: Set X).indicator (A.indicator <|
        adjointCarlesonSum (t u) ((𝓘 u:Set X).indicator g)) x‖ ^ 2) := by
      rw [integral_finset_sum,ENNReal.ofReal_sum_of_nonneg ]
      · intros
        apply integral_nonneg
        intro x
        positivity
      · intro u hu
        simp_rw [pow_two]
        apply fun h => (BoundedCompactSupport.mul h h).integrable
        apply BoundedCompactSupport.norm
        apply BoundedCompactSupport.indicator _ coeGrid_measurable
        apply BoundedCompactSupport.indicator _ hA
        exact (hg.indicator coeGrid_measurable).adjointCarlesonSum
  _ = _ := by
    simp_rw [norm_indicator_eq_indicator_norm,pow_two,← Set.indicator_mul, ← pow_two,
      integral_indicator (coeGrid_measurable)]

lemma part_3 (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) {A : Set X} (ha : MeasurableSet A)
      (j : ℕ):
    ∑ u ∈ {p | p ∈ rowDecomp t j}, ENNReal.ofReal (∫ x in (𝓘 u : Set X),
      ‖ (A.indicator (adjointCarlesonSum (t u) ((𝓘 u : Set X).indicator g)) x)‖ ^ 2)
    ≤ ∑ u ∈ {p | p ∈ rowDecomp t j}, (eLpNorm (A.indicator
      (adjointCarlesonSum (t u) (G.indicator ((𝓘 u : Set X).indicator g)))) 2 volume) ^ 2 := by
  calc
  _ ≤ ∑ u ∈ {p | p ∈ rowDecomp t j}, ENNReal.ofReal (∫ (x:X),
      ‖ (A.indicator (adjointCarlesonSum (t u) ((𝓘 u : Set X).indicator g)) x)‖ ^ 2) := by
    gcongr
    refine setIntegral_le_integral ?_ ?_
    · apply BoundedCompactSupport.integrable
      simp_rw [pow_two]
      apply fun h => BoundedCompactSupport.mul h h
      apply BoundedCompactSupport.norm
      apply BoundedCompactSupport.indicator _ ha
      exact (hg.indicator coeGrid_measurable).adjointCarlesonSum
    · rw [Filter.EventuallyLE]
      apply Filter.Eventually.of_forall
      intros
      positivity
  _ = ∑ u ∈ {p | p ∈ rowDecomp t j}, (eLpNorm (A.indicator
      (adjointCarlesonSum (t u) (G.indicator ((𝓘 u : Set X).indicator g)))) 2 volume) ^ 2 := by
    apply Finset.sum_congr rfl
    intros
    rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by finiteness) ?memLp]
    case memLp =>
      apply BoundedCompactSupport.memLp _ 2
      apply BoundedCompactSupport.indicator _ ha
      apply BoundedCompactSupport.adjointCarlesonSum
      apply BoundedCompactSupport.indicator _ measurableSet_G
      exact hg.indicator coeGrid_measurable
    rw [← ENNReal.ofReal_pow (by positivity),← Real.rpow_two,← Real.rpow_mul (by positivity)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, IsUnit.inv_mul_cancel, Real.rpow_one]
    have : G.indicator g = g:= by
      rw [Set.indicator_eq_self]
      exact h2g
    nth_rw 1 [← this]
    simp_rw [Set.indicator_indicator, Set.inter_comm G]


lemma part_123 (hg : BoundedCompactSupport g) (h2g : support g ⊆ G) {A : Set X}
    (ha : MeasurableSet A) (j : ℕ):
  (eLpNorm (A.indicator <| ∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) g) 2 volume) ^ 2
  ≤ ∑ u ∈ {p | p ∈ rowDecomp t j}, (eLpNorm (A.indicator
      (adjointCarlesonSum (t u) (G.indicator ((𝓘 u : Set X).indicator g)))) 2 volume) ^ 2 := by
  rw [part_1,part_2 hg ha]
  exact part_3 hg h2g ha j

omit [MetricSpace X] in
lemma support_subset_of_norm_le_indicator {g : X → ℝ} {A : Set X} (h2f : ∀ x, ‖f x‖ ≤ A.indicator g x) :
    f.support ⊆ A := by
  intro x hx
  contrapose! hx
  simp only [mem_support, ne_eq, Decidable.not_not]
  specialize h2f x
  simp only [indicator_of_not_mem hx,norm_le_zero_iff] at h2f
  exact h2f

-- move, give better name
omit [TileStructure Q D κ S o] in
lemma sum_disjoint_indicator_eLpNorm_le_eLpNorm (hg : BoundedCompactSupport g) {ι : Type*}
  (s : Finset ι) {f : ι → Set X} (hf : ∀ i ∈ s, MeasurableSet (f i))
    (hdisjoint : (s:Set ι).PairwiseDisjoint f) : ∑ u ∈ s, (
    eLpNorm ((f u : Set X).indicator g) 2 volume) ^ 2 ≤ (eLpNorm g 2 volume) ^ 2 :=
  calc _
  _ = ∑ u ∈ s,ENNReal.ofReal (∫ (x : X) in (f u : Set X), ‖g x‖ ^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [((hg.indicator (hf u hu)).memLp 2).eLpNorm_eq_integral_rpow_norm (by norm_num)
      (by finiteness)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← ENNReal.rpow_two,← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← ENNReal.rpow_mul, inv_mul_cancel₀ (by norm_num),ENNReal.rpow_one]
    rw [← integral_indicator (hf u hu)]
    simp_rw [pow_two,norm_indicator_eq_indicator_norm,Set.indicator_mul]
  _ = ENNReal.ofReal (∫ (x : X) in (⋃ u ∈ s, f u),
      ‖g x‖ ^2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    rw [integral_finset_biUnion _ hf]
    · exact hdisjoint
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, pow_two]
      exact fun _ _ => (hg.norm.mul hg.norm).integrable.integrableOn
  _ ≤ ENNReal.ofReal (∫ (x : X), ‖g x‖ ^2) := by
    gcongr
    simp_rw [pow_two]
    apply setIntegral_le_integral ((hg.norm.mul hg.norm).integrable)
    rw [Filter.EventuallyLE]
    apply Filter.Eventually.of_forall
    intros
    simp only [Pi.zero_apply, Pi.mul_apply, ← pow_two]
    positivity
  _ = (eLpNorm g 2 volume)^2 := by
    rw [(hg.memLp 2).eLpNorm_eq_integral_rpow_norm (by norm_num) (by finiteness)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← ENNReal.rpow_two,← ENNReal.rpow_mul,inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one]

/-- Part of Lemma 7.7.2. -/
lemma row_bound (_ : j < 2 ^ n) (hg : BoundedCompactSupport g)
    (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) g) 2 volume ≤
    C7_7_2_1 a n * eLpNorm g 2 volume := by
  calc
    eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) g) 2 volume
    = eLpNorm (Set.univ.indicator <|
      ∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) g) 2 volume := by
      rw [indicator_univ]

  _ ≤ (∑ u ∈ {p | p ∈ rowDecomp t j}, (eLpNorm (Set.univ.indicator
      (adjointCarlesonSum (t u) (G.indicator ((𝓘 u : Set X).indicator g)))) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
      apply _root_.ENNReal.le_of_pow_le_pow (by norm_num : 2 ≠ 0)
      simp_rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul,inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
        ENNReal.rpow_one]
      simp_rw [ENNReal.rpow_two]
      exact part_123 (t := t) hg (support_subset_of_norm_le_indicator h2g) (.univ) j
  _ ≤ (∑ u ∈ {p | p ∈ rowDecomp t j}, (C7_7_2_1 a n *
      eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
    simp only [indicator_univ]
    gcongr
    rename_i u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact adjoint_C7_7_2_bound1 (mem_forest_of_mem hu) (hg.indicator coeGrid_measurable)
  _ = C7_7_2_1 a n * (∑ u ∈ {p | p ∈ rowDecomp t j}, (
      eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2) ^ (2⁻¹ : ℝ) := by
    simp_rw [mul_pow (C7_7_2_1 _ _ : ℝ≥0∞), ← Finset.mul_sum,ENNReal.mul_rpow_of_nonneg (_ ^ _) _
      (by positivity : (0:ℝ) ≤ 2⁻¹)]
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num),ENNReal.rpow_one]
  _ ≤ C7_7_2_1 a n * ((eLpNorm g 2 volume) ^2) ^(2⁻¹:ℝ) := by
    gcongr
    apply sum_disjoint_indicator_eLpNorm_le_eLpNorm hg _ (fun _ _ => coeGrid_measurable)
    simp only [mem_rowDecomp_iff_mem_rowDecomp_𝔘, Finset.coe_filter, Finset.mem_univ, true_and,
      setOf_mem_eq]
    exact rowDecomp_𝔘_pairwiseDisjoint t j
  _ = C7_7_2_1 a n * (eLpNorm g 2 volume) := by
    simp_rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
      ENNReal.rpow_one]


/-- Part of Lemma 7.7.2. -/
lemma indicator_row_bound (_ : j < 2 ^ n) (hg : BoundedCompactSupport g)
    (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j}, (F.indicator <| adjointCarlesonSum (t u) g)) 2 volume ≤
    C7_7_2_2 a n * dens₂ (⋃ u ∈ t, t u) ^ (2 : ℝ)⁻¹ * eLpNorm g 2 volume := by
  calc eLpNorm (∑ u ∈ {p | p ∈ rowDecomp t j}, (F.indicator <| adjointCarlesonSum (t u) g)) 2 volume
  _ = eLpNorm (F.indicator <| ∑ u ∈ {p | p ∈ rowDecomp t j}, (adjointCarlesonSum (t u) g)) 2 volume := by
    rw [Finset.indicator_sum {p | p ∈ rowDecomp t j} F]
  _ ≤ (∑ u ∈ {p | p ∈ rowDecomp t j}, (eLpNorm (F.indicator <|
      (adjointCarlesonSum (t u) (G.indicator ((𝓘 u : Set X).indicator g)))) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
      apply _root_.ENNReal.le_of_pow_le_pow (by norm_num : 2 ≠ 0)
      simp_rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul,inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
        ENNReal.rpow_one]
      simp_rw [ENNReal.rpow_two,]
      exact part_123 (t := t) hg (support_subset_of_norm_le_indicator h2g) (measurableSet_F) j
  _ ≤ (∑ u ∈ {p | p ∈ rowDecomp t j}, (C7_7_2_2 a n * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
      eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
    gcongr
    rename_i u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact adjoint_C7_7_2_bound2 (mem_forest_of_mem hu) (hg.indicator coeGrid_measurable)
  _ ≤ (∑ u ∈ {p | p ∈ rowDecomp t j}, (C7_7_2_2 a n * ((⨆ u' ∈ rowDecomp t j, dens₂ (t u')) ^ (2 : ℝ)⁻¹) *
      eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2)^(2⁻¹:ℝ) := by
    gcongr
    rename_i u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    apply le_biSup _ hu
  _ = C7_7_2_2 a n * ((⨆ u' ∈ rowDecomp t j, dens₂ (t u')) ^ (2 : ℝ)⁻¹) *
      (∑ u ∈ {p | p ∈ rowDecomp t j},
      (eLpNorm ((𝓘 u : Set X).indicator g) 2 volume) ^ 2) ^ (2⁻¹ : ℝ) := by
    simp_rw [mul_pow (_ * _), ← Finset.mul_sum,
      ENNReal.mul_rpow_of_nonneg (_ ^ _) _ (by positivity : (0:ℝ) ≤ 2⁻¹)]
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num),ENNReal.rpow_one]
  _ ≤ C7_7_2_2 a n * ((⨆ u' ∈ rowDecomp t j, dens₂ (t u')) ^ (2 : ℝ)⁻¹) *
      ((eLpNorm g 2 volume) ^2) ^(2⁻¹:ℝ) := by
    gcongr
    apply sum_disjoint_indicator_eLpNorm_le_eLpNorm hg _ (fun _ _ => coeGrid_measurable)
    simp only [mem_rowDecomp_iff_mem_rowDecomp_𝔘, Finset.coe_filter, Finset.mem_univ, true_and,
      setOf_mem_eq]
    exact rowDecomp_𝔘_pairwiseDisjoint t j
  _ = C7_7_2_2 a n * ((⨆ u' ∈ rowDecomp t j, dens₂ (t u')) ^ (2 : ℝ)⁻¹) * (eLpNorm g 2 volume) := by
    simp_rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
      ENNReal.rpow_one]
  _ ≤ C7_7_2_2 a n * ((⨆ u' ∈ t, dens₂ (t u')) ^ (2 : ℝ)⁻¹) * (eLpNorm g 2 volume) := by
    gcongr _ * ?_ ^ _ * _
    apply biSup_mono
    exact fun _ => mem_forest_of_mem
  _ = _ := by
    congr 3
    rw [dens₂_eq_biSup_dens₂]
    simp_rw [dens₂_eq_biSup_dens₂ (⇑t _), iSup_iUnion]


/-- The constant used in `row_correlation`.
Has value `2 ^ (862 * a ^ 3 - 3 * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_7_3 (a n : ℕ) : ℝ≥0 := 2 ^ (862 * (a : ℝ) ^ 3 - 2 * n)

/-- Lemma 7.7.3. -/
lemma row_correlation (hjj' : j < j') (hj' : j' < 2 ^ n)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁) (h3f₁ : ∀ x, ‖f₁ x‖ ≤ G.indicator 1 x)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) (h3f₂ : ∀ x, ‖f₂ x‖ ≤ G.indicator 1 x) :
    ‖∫ x, (∑ u ∈ {p | p ∈ rowDecomp t j}, adjointCarlesonSum (t u) f₁ x) *
    (∑ u ∈ {p | p ∈ rowDecomp t j'}, adjointCarlesonSum (t u) f₂ x)‖₊ ≤
    C7_7_3 a n * eLpNorm f₁ 2 volume * eLpNorm f₂ 2 volume := by
  sorry

variable (t) in
/-- The definition of `Eⱼ` defined above Lemma 7.7.4. -/
def rowSupport (j : ℕ) : Set X := ⋃ (u ∈ rowDecomp t j) (p ∈ t u), E p

lemma disjoint_impl {p p' : 𝔓 X} : Disjoint (Ω p) (Ω p') → Disjoint (E p) (E p') := by
  simp_rw [Set.disjoint_iff,subset_def]
  intro h x hx
  exact h (Q x) ⟨Q_mem_Ω hx.left, Q_mem_Ω hx.right⟩

lemma disjoint_of_ne_of_mem {i j : ℕ} {u u' : 𝔓 X} (hne : u ≠ u') (hu : u ∈ t.rowDecomp i) (hu' : u' ∈ t.rowDecomp j)
  {p p' : 𝔓 X} (hp : p ∈ t u) (hp' : p' ∈ t u') : Disjoint (E p) (E p') := by
  wlog hsle : 𝔰 p ≤ 𝔰 p'
  · exact (this hne.symm hu' hu hp' hp (Int.le_of_not_le hsle)).symm
  -- if x is in the inter, both `Disjoint (Ω p) (Ω p')` and `Q x ∈ Ω p ∩ Ω p'`
  refine _root_.not_imp_self.mp (fun h => disjoint_impl ?_)
  simp only [Set.disjoint_iff, subset_def, mem_inter_iff, mem_empty_iff_false, imp_false, not_and,
    not_forall, Decidable.not_not] at h
  obtain ⟨x,hxp, hxp'⟩ := h
  rw [← rowDecomp_apply (j := j)] at hp'
  have 𝓘_p_le : 𝓘 p ≤ 𝓘 p' := by
    exact ⟨(fundamental_dyadic hsle).resolve_right <|
      Set.Nonempty.not_disjoint <|
      Set.nonempty_of_mem ⟨E_subset_𝓘 hxp,E_subset_𝓘 hxp'⟩, hsle⟩
  have : 2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u') := lt_dist t
    (mem_forest_of_mem hu') (mem_forest_of_mem hu) hne.symm hp
    <| le_trans 𝓘_p_le (𝓘_le_𝓘 _ hu' hp')
  have := calc 2 ^ (Z * (n + 1)) - 4
    _ < dist_(p) (𝒬 p) (𝒬 u') - dist_(p) (𝒬 p') (𝒬 u') :=
      sub_lt_sub this <| lt_of_le_of_lt (Grid.dist_mono 𝓘_p_le) <| dist_lt_four _ hu' hp'
    _ ≤ dist_(p) (𝒬 p) (𝒬 p') := by
      exact le_trans (le_abs_self _) <|
        abs_dist_sub_le (α := WithFunctionDistance (𝔠 p) (↑D ^ 𝔰 p / 4)) _ _ _
  have : 𝒬 p' ∉ ball_(p) (𝒬 p) 1 := by
    rw [mem_ball (α := WithFunctionDistance (𝔠 p) (↑D ^ 𝔰 p / 4)),dist_comm]
    exact not_lt_of_le <| le_trans (calculation_7_7_4 (X := X)) this.le
  have : ¬(Ω p' ⊆ Ω p) := (fun hx => this <| subset_cball <| hx 𝒬_mem_Ω)
  exact (relative_fundamental_dyadic 𝓘_p_le).resolve_right this

/-- Lemma 7.7.4 -/
lemma pairwiseDisjoint_rowSupport :
    (Iio (2 ^ n)).PairwiseDisjoint (rowSupport t) := by
  intro i hi j hj hne
  have rowDecomp_disjoint : Disjoint (α := Set (𝔓 X)) (t.rowDecomp i) (t.rowDecomp j) := by
    exact (pairwiseDisjoint_rowDecomp (t := t) hi hj hne)
  clear hi hj hne
  dsimp [onFun, rowSupport]
  simp only [disjoint_iUnion_right, disjoint_iUnion_left]
  intro u hu p hp u' hu' p' hp'
  exact disjoint_of_ne_of_mem (rowDecomp_disjoint.ne_of_mem hu' hu) hu' hu hp' hp


end TileStructure.Forest

/-! ## Proposition 2.0.4 -/

irreducible_def C2_0_4_base (a : ℝ) : ℝ≥0 := 2 ^ (432 * a ^ 3)

/-- The constant used in `forest_operator`.
Has value `2 ^ (432 * a ^ 3 - (q - 1) / q * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C2_0_4 (a q : ℝ) (n : ℕ) : ℝ≥0 := C2_0_4_base a * 2 ^ (- (q - 1) / q * n)

theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g)
    (h2g : IsBounded (support g)) :
    ‖∫ x, conj (g x) * ∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

/-- Version of the forest operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function. -/
theorem forest_operator' {n : ℕ} (𝔉 : Forest X n) {f : X → ℂ} {A : Set X}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : MeasurableSet A)
    (h'A : IsBounded A) :
    ∫⁻ x in A, ‖∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * (volume A) ^ (1/2 : ℝ) := by
  /- This follows from the other version by taking for the test function `g` the argument of
  the sum to be controlled. -/
  rw [← ennnorm_integral_starRingEnd_mul_eq_lintegral_ennnorm]; swap
  · apply BoundedCompactSupport.integrable
    apply BoundedCompactSupport.finset_sum (fun i hi ↦ ?_)
    apply BoundedCompactSupport.carlesonSum
    have : BoundedCompactSupport (F.indicator 1 : X → ℝ) := by
      apply BoundedCompactSupport.indicator_of_isBounded_range _ stronglyMeasurable_one _
        measurableSet_F
      · exact isBounded_range_iff_forall_norm_le.2 ⟨1, fun x ↦ by simp⟩
      · exact isBounded_F
    apply BoundedCompactSupport.mono this hf.stronglyMeasurable h2f
  rw [← integral_indicator hA]
  simp_rw [indicator_mul_left, ← comp_def,
    Set.indicator_comp_of_zero (g := starRingEnd ℂ) (by simp)]
  apply (forest_operator 𝔉 hf h2f ?_ ?_).trans; rotate_left
  · apply Measurable.indicator _ hA
    fun_prop
  · apply h'A.subset support_indicator_subset
  gcongr
  · simp only [sub_nonneg, ge_iff_le, inv_le_inv₀ zero_lt_two (q_pos X)]
    exact (q_mem_Ioc (X := X)).2
  · exact le_rfl
  calc
  _ ≤ eLpNorm (A.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    simp only [indicator, coe_algebraMap, Pi.one_apply, Real.norm_eq_abs]
    split_ifs
    · have A (x : ℝ) : x / x ≤ 1 := by
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · simp [hx]
      simpa using A _
    · simp
  _ ≤ _ := by
    rw [eLpNorm_indicator_const]
    · simp
    · exact hA
    · norm_num
    · norm_num

/-- Version of the forest operator theorem, but controlling the integral of the norm instead of
the integral of the function multiplied by another function, and with the upper bound in terms
of `volume F` and `volume G`.  -/
theorem forest_operator_le_volume {n : ℕ} (𝔉 : Forest X n) {f : X → ℂ} {A : Set X}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hA : MeasurableSet A)
    (h'A : IsBounded A) :
    ∫⁻ x in A, ‖∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (⋃ u ∈ 𝔉, 𝔉 u)) ^ (q⁻¹ - 2⁻¹) *
    (volume F) ^ (1/2 : ℝ) * (volume A) ^ (1/2 : ℝ) := by
  apply (forest_operator' 𝔉 hf h2f hA h'A).trans
  gcongr
  calc
  _ ≤ eLpNorm (F.indicator (fun x ↦ 1) : X → ℝ) 2 volume := by
    apply eLpNorm_mono (fun x ↦ ?_)
    apply (h2f x).trans (le_abs_self _)
  _ ≤ _ := by
    rw [eLpNorm_indicator_const]
    · simp
    · exact measurableSet_F
    · norm_num
    · norm_num
