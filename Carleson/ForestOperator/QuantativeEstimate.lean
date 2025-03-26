import Carleson.ForestOperator.L2Estimate
import Carleson.ToMathlib.BoundedCompactSupport

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

/-! ## Section 7.3 and Lemma 7.3.1 -/

/-- The constant used in `local_dens1_tree_bound`.
Has value `2 ^ (101 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_2 (a : ℕ) : ℝ≥0 := 2 ^ (101 * (a : ℝ) ^ 3)

/-- Lemma 7.3.2. -/
lemma local_dens1_tree_bound (hu : u ∈ t) (hL : L ∈ 𝓛 (t u)) :
    volume (L ∩ G ∩ ⋃ (p ∈ t u), E p) ≤ C7_3_2 a * dens₁ (t u) * volume (L : Set X) := by
  sorry

/-- The constant used in `local_dens2_tree_bound`.
Has value `2 ^ (200 * a ^ 3 + 19)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
-- feel free to modify the constant to something simpler.
irreducible_def C7_3_3 (a : ℕ) : ℝ≥0 := 2 ^ (201 * (a : ℝ) ^ 3)

/-- Lemma 7.3.3. -/
lemma local_dens2_tree_bound (hJ : J ∈ 𝓙 (t u)) {q : 𝔓 X} (hq : q ∈ t u)
    (hJq : ¬ Disjoint (J : Set X) (𝓘 q)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t u) * volume (J : Set X) := by
  sorry

/-- The constant used in `density_tree_bound1`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_1_1 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- First part of Lemma 7.3.1. -/
lemma density_tree_bound1
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g)
    (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_1 a *  dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

omit [TileStructure Q D κ S o] in
-- move somewhere else
lemma _root_.MeasureTheory.BoundedCompactSupport.const_smul (hf : BoundedCompactSupport f) (c : ℝ) :
  BoundedCompactSupport (c • f) := by
  simp_rw [Pi.smul_def,Complex.real_smul]
  apply hf.const_mul

omit [TileStructure Q D κ S o] [MetricSpace X] in
-- rename, move somewhere else
lemma smul_le_indicator {A : Set X} (hf : f.support ⊆ A) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hCpos : 0 < C):
  ∀ x, ‖(C⁻¹ • f) x‖ ≤ A.indicator 1 x := by
  intro x
  simp only [Pi.smul_apply, real_smul, ofReal_inv, Complex.norm_mul, norm_inv, norm_real,
    Real.norm_eq_abs]
  rw [inv_mul_le_iff₀ (by positivity),mul_comm,← indicator_mul_const]
  simp only [Pi.one_apply, one_mul]
  if h : x ∈ A then
    rw [indicator_of_mem h]
    exact le_trans (hC x) (by exact le_abs_self C)
  else
    rw [nmem_support.mp (fun a ↦ h (hf a)), indicator_of_not_mem h]
    simp only [norm_zero, le_refl]

/--
`density_tree_bound1` with support assumptions rather than indicator assumptions.
-/
lemma density_tree_bound1'
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g)
    (hg2 : g.support ⊆ G) (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_1 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  obtain ⟨C,hCpos,hC⟩ := hg.isBounded.exists_pos_norm_le
  simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hC
  have : BoundedCompactSupport (C⁻¹ • g) := hg.const_smul _
  have : ∀ x, ‖(C⁻¹ • g) x‖ ≤ G.indicator 1 x := smul_le_indicator hg2 hC hCpos
  have := density_tree_bound1 hf (by assumption) this hu
  rw [← enorm_eq_nnnorm] at this ⊢
  simp_rw [Pi.smul_apply,starRingEnd_apply,star_smul,smul_mul_assoc,
    integral_smul,star_trivial] at this
  rw [_root_.enorm_smul,eLpNorm_const_smul] at this
  simp only [defaultA, RCLike.star_def] at this
  ring_nf at this ⊢
  simp_rw [mul_assoc] at this ⊢
  apply ENNReal.mul_le_mul_left _ (enorm_ne_top) |>.mp this
  · apply enorm_ne_zero.mpr
    positivity

/-- The constant used in `density_tree_bound2`.
Has value `2 ^ (256 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_3_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (256 * (a : ℝ) ^ 3)

/-- Second part of Lemma 7.3.1. -/
lemma density_tree_bound2 -- some assumptions on f are superfluous
    (hf : BoundedCompactSupport f)
    (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : BoundedCompactSupport g)
    (h2g : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

/--
`density_tree_bound2` with support assumptions rather than indicator assumptions.
-/
lemma density_tree_bound2'
    (hf : BoundedCompactSupport f)
    (h2f : support f ⊆ F)
    (hg : BoundedCompactSupport g)
    (h2g : support g ⊆ G)
    (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_3_1_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * dens₂ (t u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  obtain ⟨Cf,hCfpos,hCf⟩ := hf.isBounded.exists_pos_norm_le
  obtain ⟨Cg,hCgpos,hCg⟩ := hg.isBounded.exists_pos_norm_le
  simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hCf hCg
  have hf_smul : BoundedCompactSupport (Cf⁻¹ • f) := hf.const_smul _
  have : ∀ x, ‖(Cf⁻¹ • f) x‖ ≤ F.indicator 1 x := smul_le_indicator h2f hCf hCfpos
  have hg_smul : BoundedCompactSupport (Cg⁻¹ • g) := hg.const_smul _
  have : ∀ x, ‖(Cg⁻¹ • g) x‖ ≤ G.indicator 1 x := smul_le_indicator h2g hCg hCgpos
  have := density_tree_bound2 hf_smul (by assumption) hg_smul (by assumption) hu
  rw [← enorm_eq_nnnorm] at this ⊢
  simp_rw [carlesonSum_const_smul,Pi.smul_apply,starRingEnd_apply,star_smul,smul_mul_assoc,
    mul_smul_comm,star_trivial,smul_smul,integral_smul] at this
  rw [_root_.enorm_smul,eLpNorm_const_smul,eLpNorm_const_smul] at this
  simp only [defaultA, RCLike.star_def,_root_.enorm_mul] at this
  ring_nf at this ⊢
  simp_rw [mul_assoc] at this ⊢
  simp_rw [← mul_assoc ‖Cg⁻¹‖ₑ,← _root_.enorm_mul] at this
  apply ENNReal.mul_le_mul_left _ (enorm_ne_top) |>.mp this
  · apply enorm_ne_zero.mpr
    positivity


end TileStructure.Forest
