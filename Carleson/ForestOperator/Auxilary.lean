import Carleson.ForestOperator.AlmostOrthogonality

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n : ℕ} {t : Forest X n} {u₁ u₂ : 𝔓 X} {𝔖 : Set (𝔓 X)}



noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

variable (u₁ 𝔖) in
def 𝓙_sub : Set (Grid X) := 𝓙 𝔖 ∩ Iic (𝓘 u₁)

variable (u₁) in
lemma union_𝓙_sub_subset :
  ⋃ J ∈ 𝓙_sub u₁ 𝔖, (J : Set X) ⊆ 𝓘 u₁ := iUnion₂_subset (fun _ hJ ↦ hJ.2.1)

lemma subset_union_𝓙_sub (hu₁ : u₁ ∈ t) (h : t u₁ ⊆ 𝔖) :
    (𝓘 u₁ : Set X) ⊆ ⋃ J ∈ 𝓙_sub u₁ 𝔖, (J : Set X) := by
  intro x hx
  have existsCube : x ∈ ⋃ J ∈ 𝓙 𝔖, (J : Set X) := by
    rw [biUnion_𝓙 (𝔖 := 𝔖)]
    exact subset_iUnion _ (𝓘 u₁) hx
  simp only [mem_iUnion, exists_prop] at existsCube ⊢
  rcases existsCube with ⟨cube,cube_in_𝓙,xInCube⟩
  have notDisjoint := Set.not_disjoint_iff.mpr ⟨x, xInCube, hx⟩
  have cubeIn𝓙₀ : cube ∈ 𝓙₀ 𝔖 := mem_of_mem_inter_left cube_in_𝓙
  simp only [mem_setOf_eq] at cubeIn𝓙₀
  cases cubeIn𝓙₀ with
  | inl west =>
    refine ⟨cube, ?_, xInCube⟩
    refine ⟨cube_in_𝓙, ?_⟩
    simp only [mem_Iic, Grid.le_def]
    have smaller := calc s cube
      _ = -S := west
      _ ≤ s (𝓘 u₁) := (mem_Icc.mp (scale_mem_Icc (i := 𝓘 u₁))).left
    refine ⟨?_, smaller⟩
    cases GridStructure.fundamental_dyadic' smaller with
    | inl subset => exact subset
    | inr disjoint => exact (notDisjoint disjoint).elim
  | inr east =>
    obtain ⟨p, belongs⟩ := t.nonempty' hu₁
    by_contra! contr
    have black : ¬(𝓘 p : Set X) ⊆ ball (c cube) (100 * D ^ (s cube + 1)) :=
      east p (h belongs)
    have white := calc (𝓘 p : Set X)
      _ ⊆ 𝓘 u₁ := (𝓘_le_𝓘 t hu₁ belongs).left
      _ ⊆ cube := by
        apply subset_of_nmem_Iic_of_not_disjoint cube
        · have notIn : cube ∉ 𝓙_sub u₁ 𝔖 := λ a => contr cube a xInCube
          rw [𝓙_sub, inter_def, Set.mem_setOf_eq, not_and_or] at notIn
          exact Or.resolve_left notIn (Set.not_not_mem.mpr cube_in_𝓙)
        · exact notDisjoint
      _ ⊆ ball (c cube) (4 * D ^ s cube) := by
        exact Grid_subset_ball (i := cube)
      _ ⊆ ball (c cube) (100 * D ^ (s cube + 1)) := by
        unfold ball
        intro y xy
        rw [mem_setOf_eq] at xy ⊢
        have numbers : 4 * (D : ℝ) ^ s cube < 100 * D ^ (s cube + 1) := by
          gcongr
          linarith
          exact one_lt_D (X := X)
          linarith
        exact gt_trans numbers xy
    contradiction

-- variable (t u₁) in
def union_𝓙_sub_eq (hu₁ : u₁ ∈ t) (h :t u₁ ⊆ 𝔖):
    ⋃ J ∈ 𝓙_sub u₁ 𝔖, (J : Set X) = 𝓘 u₁ := by
  apply Set.Subset.antisymm
  · exact union_𝓙_sub_subset u₁
  · exact subset_union_𝓙_sub hu₁ h

-- variable (t u₁) in
lemma union_𝓙₅ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    ⋃ J ∈ 𝓙_sub u₁ (𝔖₀ t u₁ u₂), (J : Set X) = 𝓘 u₁ := by
  apply union_𝓙_sub_eq hu₁
  apply 𝔗_subset_𝔖₀ hu₁ hu₂ hu h2u

-- variable (t u₁) in
lemma union_𝓙₆ (hu₁ : u₁ ∈ t):
    ⋃ J ∈ 𝓙_sub u₁ (t u₁), (J : Set X) = 𝓘 u₁ := by
  apply union_𝓙_sub_eq hu₁
  exact subset_refl _


end TileStructure.Forest
end
