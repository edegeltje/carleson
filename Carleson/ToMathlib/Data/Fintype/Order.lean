import Mathlib.Data.Fintype.Order

-- these aren't actually used anymore in carleson, but they still might be good to have in mathlib

-- uses [Finite (Set α)] in order to skip having to import `Finite.instSet`
lemma Finite.exists_maximal_and_mem {α : Type*} [Finite (Set α)] {p : (Set α) → Prop}
    {b : Set α} (hb : p b) {x : α} (hx : x ∈ b) : ∃ m, Maximal (p ·) m ∧ x ∈ m :=
  (Finite.exists_le_maximal (p := fun _ => _ ∧ _) ⟨hb,hx⟩).imp
    fun _ ⟨hl,hm⟩ =>
      ⟨⟨hm.prop.left,fun _ hm' hle => hm.le_of_ge ⟨hm',hm.prop.right⟩ hle⟩,hl hm.prop.right⟩


lemma Set.Finite.exists_maximal_and_mem {α : Type*} {s : Set (Set α)} (hs : s.Finite)
    {b : Set α} (hb : b ∈ s) {x : α} (hx : x ∈ b) : ∃ m, Maximal (· ∈ s) m ∧ x ∈ m :=
  (hs.inter_of_left _ |>.exists_le_maximal (s := s ∩ {y' | x ∈ y'}) ⟨hb,hx⟩).imp
    fun _ ⟨_,hm⟩ =>
      ⟨⟨hm.prop.left,fun _ hm' hle => hm.le_of_ge ⟨hm',hle hm.prop.right⟩ hle⟩,hm.prop.right⟩

-- note : The Finset version of this statement needs [∀ s' ∈ s, Decidable (x ∈ s)].
-- this makes it useless as a lemma, because this is not a possible instance argument.
-- as such, that version is not written here.
