/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds

/-!
# Noetherian space

A Noetherian space is a topological space that satisfies any of the following equivalent conditions:
- `WellFounded ((· > ·) : TopologicalSpace.Opens α → TopologicalSpace.Opens α → Prop)`
- `WellFounded ((· < ·) : TopologicalSpace.Closeds α → TopologicalSpace.Closeds α → Prop)`
- `∀ s : Set α, IsCompact s`
- `∀ s : TopologicalSpace.Opens α, IsCompact s`

The first is chosen as the definition, and the equivalence is shown in
`TopologicalSpace.noetherianSpace_TFAE`.

Many examples of noetherian spaces come from algebraic topology. For example, the underlying space
of a noetherian scheme (e.g., the spectrum of a noetherian ring) is noetherian.

## Main Results

- `TopologicalSpace.NoetherianSpace.set`: Every subspace of a noetherian space is noetherian.
- `TopologicalSpace.NoetherianSpace.isCompact`: Every set in a noetherian space is a compact set.
- `TopologicalSpace.noetherianSpace_TFAE`: Describes the equivalent definitions of noetherian
  spaces.
- `TopologicalSpace.NoetherianSpace.range`: The image of a noetherian space under a continuous map
  is noetherian.
- `TopologicalSpace.NoetherianSpace.iUnion`: The finite union of noetherian spaces is noetherian.
- `TopologicalSpace.NoetherianSpace.discrete`: A noetherian and Hausdorff space is discrete.
- `TopologicalSpace.NoetherianSpace.exists_finset_irreducible`: Every closed subset of a noetherian
  space is a finite union of irreducible closed subsets.
- `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`: The number of irreducible
  components of a noetherian space is finite.

-/

open Topology

variable (α β : Type*) [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-- Type class for noetherian spaces. It is defined to be spaces whose open sets satisfies ACC. -/
abbrev NoetherianSpace : Prop := WellFoundedGT (Opens α)

theorem noetherianSpace_iff_opens : NoetherianSpace α ↔ ∀ s : Opens α, IsCompact (s : Set α) := by
  rw [NoetherianSpace, CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact,
    CompleteLattice.isSupFiniteCompact_iff_all_elements_compact]
  exact forall_congr' Opens.isCompactElement_iff

instance (priority := 100) NoetherianSpace.compactSpace [h : NoetherianSpace α] : CompactSpace α :=
  ⟨(noetherianSpace_iff_opens α).mp h ⊤⟩

variable {α β}

/-- In a Noetherian space, all sets are compact. -/
protected theorem NoetherianSpace.isCompact [NoetherianSpace α] (s : Set α) : IsCompact s := by
  refine isCompact_iff_finite_subcover.2 fun U hUo hs => ?_
  rcases ((noetherianSpace_iff_opens α).mp ‹_› ⟨⋃ i, U i, isOpen_iUnion hUo⟩).elim_finite_subcover U
    hUo Set.Subset.rfl with ⟨t, ht⟩
  exact ⟨t, hs.trans ht⟩

protected theorem _root_.Topology.IsInducing.noetherianSpace [NoetherianSpace α] {i : β → α}
    (hi : IsInducing i) : NoetherianSpace β :=
  (noetherianSpace_iff_opens _).2 fun _ => hi.isCompact_iff.2 (NoetherianSpace.isCompact _)

@[deprecated (since := "2024-10-28")]
alias _root_.Inducing.noetherianSpace := IsInducing.noetherianSpace

@[stacks 0052 "(1)"]
instance NoetherianSpace.set [NoetherianSpace α] (s : Set α) : NoetherianSpace s :=
  IsInducing.subtypeVal.noetherianSpace

variable (α) in
open List in
theorem noetherianSpace_TFAE :
    TFAE [NoetherianSpace α,
      WellFoundedLT (Closeds α),
      ∀ s : Set α, IsCompact s,
      ∀ s : Opens α, IsCompact (s : Set α)] := by
  tfae_have 1 ↔ 2 := by
    simp_rw [isWellFounded_iff]
    exact Opens.compl_bijective.2.wellFounded_iff (@OrderIso.compl (Set α)).lt_iff_lt.symm
  tfae_have 1 ↔ 4 := noetherianSpace_iff_opens α
  tfae_have 1 → 3 := @NoetherianSpace.isCompact α _
  tfae_have 3 → 4 := fun h s => h s
  tfae_finish

theorem noetherianSpace_iff_isCompact : NoetherianSpace α ↔ ∀ s : Set α, IsCompact s :=
  (noetherianSpace_TFAE α).out 0 2

instance [NoetherianSpace α] : WellFoundedLT (Closeds α) :=
  Iff.mp ((noetherianSpace_TFAE α).out 0 1) ‹_›

instance {α} : NoetherianSpace (CofiniteTopology α) := by
  simp only [noetherianSpace_iff_isCompact, isCompact_iff_ultrafilter_le_nhds,
    CofiniteTopology.nhds_eq, Ultrafilter.le_sup_iff, Filter.le_principal_iff]
  intro s f hs
  rcases f.le_cofinite_or_eq_pure with (hf | ⟨a, rfl⟩)
  · rcases Filter.nonempty_of_mem hs with ⟨a, ha⟩
    exact ⟨a, ha, Or.inr hf⟩
  · exact ⟨a, hs, Or.inl le_rfl⟩

theorem noetherianSpace_of_surjective [NoetherianSpace α] (f : α → β) (hf : Continuous f)
    (hf' : Function.Surjective f) : NoetherianSpace β :=
  noetherianSpace_iff_isCompact.2 <| (Set.image_surjective.mpr hf').forall.2 fun s =>
    (NoetherianSpace.isCompact s).image hf

theorem noetherianSpace_iff_of_homeomorph (f : α ≃ₜ β) : NoetherianSpace α ↔ NoetherianSpace β :=
  ⟨fun _ => noetherianSpace_of_surjective f f.continuous f.surjective,
    fun _ => noetherianSpace_of_surjective f.symm f.symm.continuous f.symm.surjective⟩

theorem NoetherianSpace.range [NoetherianSpace α] (f : α → β) (hf : Continuous f) :
    NoetherianSpace (Set.range f) :=
  noetherianSpace_of_surjective (Set.rangeFactorization f) (hf.subtype_mk _)
    Set.surjective_onto_range

theorem noetherianSpace_set_iff (s : Set α) :
    NoetherianSpace s ↔ ∀ t, t ⊆ s → IsCompact t := by
  simp only [noetherianSpace_iff_isCompact, IsEmbedding.subtypeVal.isCompact_iff,
    Subtype.forall_set_subtype]

@[simp]
theorem noetherian_univ_iff : NoetherianSpace (Set.univ : Set α) ↔ NoetherianSpace α :=
  noetherianSpace_iff_of_homeomorph (Homeomorph.Set.univ α)

theorem NoetherianSpace.iUnion {ι : Type*} (f : ι → Set α) [Finite ι]
    [hf : ∀ i, NoetherianSpace (f i)] : NoetherianSpace (⋃ i, f i) := by
  simp_rw [noetherianSpace_set_iff] at hf ⊢
  intro t ht
  rw [← Set.inter_eq_left.mpr ht, Set.inter_iUnion]
  exact isCompact_iUnion fun i => hf i _ Set.inter_subset_right

-- This is not an instance since it makes a loop with `t2_space_discrete`.
theorem NoetherianSpace.discrete [NoetherianSpace α] [T2Space α] : DiscreteTopology α :=
  ⟨eq_bot_iff.mpr fun _ _ => isClosed_compl_iff.mp (NoetherianSpace.isCompact _).isClosed⟩

attribute [local instance] NoetherianSpace.discrete

/-- Spaces that are both Noetherian and Hausdorff are finite. -/
theorem NoetherianSpace.finite [NoetherianSpace α] [T2Space α] : Finite α :=
  Finite.of_finite_univ (NoetherianSpace.isCompact Set.univ).finite_of_discrete

instance (priority := 100) Finite.to_noetherianSpace [Finite α] : NoetherianSpace α :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

/-- In a Noetherian space, every closed set is a finite union of irreducible closed sets. -/
theorem NoetherianSpace.exists_finite_set_closeds_irreducible [NoetherianSpace α] (s : Closeds α) :
    ∃ S : Set (Closeds α), S.Finite ∧ (∀ t ∈ S, IsIrreducible (t : Set α)) ∧ s = sSup S := by
  apply wellFounded_lt.induction s; clear s
  intro s H
  rcases eq_or_ne s ⊥ with rfl | h₀
  · use ∅; simp
  · by_cases h₁ : IsPreirreducible (s : Set α)
    · replace h₁ : IsIrreducible (s : Set α) := ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
      use {s}; simp [h₁]
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      lift z₁ to Closeds α using hz₁
      lift z₂ to Closeds α using hz₂
      rcases H (s ⊓ z₁) (inf_lt_left.2 hz₁') with ⟨S₁, hSf₁, hS₁, h₁⟩
      rcases H (s ⊓ z₂) (inf_lt_left.2 hz₂') with ⟨S₂, hSf₂, hS₂, h₂⟩
      refine ⟨S₁ ∪ S₂, hSf₁.union hSf₂, Set.union_subset_iff.2 ⟨hS₁, hS₂⟩, ?_⟩
      rwa [sSup_union, ← h₁, ← h₂, ← inf_sup_left, left_eq_inf]

/-- In a Noetherian space, every closed set is a finite union of irreducible closed sets. -/
theorem NoetherianSpace.exists_finite_set_isClosed_irreducible [NoetherianSpace α]
    {s : Set α} (hs : IsClosed s) : ∃ S : Set (Set α), S.Finite ∧
      (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧ s = ⋃₀ S := by
  lift s to Closeds α using hs
  rcases NoetherianSpace.exists_finite_set_closeds_irreducible s with ⟨S, hSf, hS, rfl⟩
  refine ⟨(↑) '' S, hSf.image _, Set.forall_mem_image.2 fun S _ ↦ S.2, Set.forall_mem_image.2 hS,
    ?_⟩
  lift S to Finset (Closeds α) using hSf
  simp [← Finset.sup_id_eq_sSup, Closeds.coe_finset_sup]

/-- In a Noetherian space, every closed set is a finite union of irreducible closed sets. -/
theorem NoetherianSpace.exists_finset_irreducible [NoetherianSpace α] (s : Closeds α) :
    ∃ S : Finset (Closeds α), (∀ k : S, IsIrreducible (k : Set α)) ∧ s = S.sup id := by
  simpa [Set.exists_finite_iff_finset, Finset.sup_id_eq_sSup]
    using NoetherianSpace.exists_finite_set_closeds_irreducible s

@[stacks 0052 "(2)"]
theorem NoetherianSpace.finite_irreducibleComponents [NoetherianSpace α] :
    (irreducibleComponents α).Finite := by
  obtain ⟨S : Set (Set α), hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible isClosed_univ (α := α)
  refine hSf.subset fun s hs => ?_
  lift S to Finset (Set α) using hSf
  rcases isIrreducible_iff_sUnion_isClosed.1 hs.1 S hSc (hSU ▸ Set.subset_univ _) with ⟨t, htS, ht⟩
  rwa [ht.antisymm (hs.2 (hSi _ htS) ht)]

@[stacks 0052 "(3)"]
theorem NoetherianSpace.exists_open_ne_empty_le_irreducibleComponent [NoetherianSpace α]
    (Z : Set α) (H : Z ∈ irreducibleComponents α) :
    ∃ o : Set α, IsOpen o ∧ o ≠ ∅ ∧ o ≤ Z := by
  classical
  let ι : Set (Set α) := irreducibleComponents α \ {Z}
  have hι : ι.Finite := NoetherianSpace.finite_irreducibleComponents.subset Set.diff_subset
  have hι' : Finite ι := by rwa [Set.finite_coe_iff]
  let U := Z \ ⋃ (x : ι), x
  have hU0 : U ≠ ∅ := fun r ↦ by
    obtain ⟨Z', hZ'⟩ := isIrreducible_iff_sUnion_isClosed.mp H.1 hι.toFinset
      (fun z hz ↦ by
        simp only [Set.Finite.mem_toFinset] at hz
        exact isClosed_of_mem_irreducibleComponents _ hz.1)
      (by
        rw [Set.Finite.coe_toFinset, Set.sUnion_eq_iUnion]
        rw [Set.diff_eq_empty] at r
        exact r)
    simp only [Set.Finite.mem_toFinset] at hZ'
    exact hZ'.1.2 <| le_antisymm (H.2 hZ'.1.1.1 hZ'.2) hZ'.2
  have hU1 : U = (⋃ (x : ι), x.1) ᶜ := by
    rw [Set.compl_eq_univ_diff]
    refine le_antisymm (Set.diff_subset_diff le_top <| subset_refl _) ?_
    rw [← Set.compl_eq_univ_diff]
    refine Set.compl_subset_iff_union.mpr (le_antisymm le_top ?_)
    rw [Set.union_comm, ← Set.sUnion_eq_iUnion, ← Set.sUnion_insert]
    rintro a -
    by_cases h : a ∈ U
    · exact ⟨U, Set.mem_insert _ _, h⟩
    · rw [Set.mem_diff, Decidable.not_and_iff_not_or_not, not_not, Set.mem_iUnion] at h
      rcases h with (h|⟨i, hi⟩)
      · refine ⟨irreducibleComponent a, Or.inr ?_, mem_irreducibleComponent⟩
        simp only [ι, Set.mem_diff, Set.mem_singleton_iff]
        refine ⟨irreducibleComponent_mem_irreducibleComponents _, ?_⟩
        rintro rfl
        exact h mem_irreducibleComponent
      · exact ⟨i, Or.inr i.2, hi⟩
  refine ⟨U, hU1 ▸ isOpen_compl_iff.mpr ?_, hU0, sdiff_le⟩
  exact isClosed_iUnion_of_finite fun i ↦ isClosed_of_mem_irreducibleComponents i.1 i.2.1

end TopologicalSpace
