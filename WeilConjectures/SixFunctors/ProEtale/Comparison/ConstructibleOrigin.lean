/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LocallyConstantOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Gluing sheaves of étale origin along a stratification

Let `X` be a quasi-compact quasi-separated scheme with a stratification `S`. The immersions of
the strata are quasi-compact, their ranges being constructible
(`Topology.IsConstructible.isCompact_of_compactSpace`), so their pullbacks jointly detect zero
pro-étale sheaves (`AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero`).
Hence a pro-étale sheaf of `Λ`-modules on `X` is of étale origin as soon as its pullbacks to
the strata are (`AlgebraicGeometry.ProEtale.essImage_comparisonUpperStar_of_stratification`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

section Constructible

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [QuasiSober X] [PrespectralSpace X]
  [QuasiSeparatedSpace X]

/-- A constructible subset of a quasi-compact, quasi-separated, quasi-sober prespectral space (for
instance of a quasi-compact quasi-separated scheme) is quasi-compact: it is closed in the
constructible topology, which is quasi-compact and finer than the topology of `X`. -/
lemma Topology.IsConstructible.isCompact_of_compactSpace {s : Set X} (hs : IsConstructible s) :
    IsCompact s := by
  have hclo : IsOpen[constructibleTopology X] s ∧ IsOpen[constructibleTopology X] sᶜ := by
    induction hs using IsConstructible.empty_union_induction with
    | open_retrocompact U hU hUc =>
      refine ⟨hUc.isCompact.isOpen_constructibleTopology_of_isOpen hU, ?_⟩
      exact IsCompact.isOpen_constructibleTopology_of_isClosed (by simpa using hUc.isCompact)
        hU.isClosed_compl
    | union s _ t _ hs ht =>
      refine ⟨@IsOpen.union _ _ _ (constructibleTopology X) hs.1 ht.1, ?_⟩
      rw [Set.compl_union]
      exact @IsOpen.inter _ (constructibleTopology X) _ _ hs.2 ht.2
    | compl s _ hs => exact ⟨hs.2, by rw [compl_compl]; exact hs.1⟩
  -- the identity from the constructible topology is continuous
  have hcont : Continuous (WithTopology.ofTopology : WithConstructibleTopology X → X) := by
    refine ⟨fun U hU ↦ WithConstructibleTopology.isOpen_iff.2 ?_⟩
    change IsOpen[constructibleTopology X] U
    rw [(PrespectralSpace.isTopologicalBasis (X := X)).open_eq_sUnion' hU]
    refine @isOpen_sUnion _ (constructibleTopology X) _ fun V hV ↦ ?_
    exact hV.1.2.isOpen_constructibleTopology_of_isOpen hV.1.1
  have hcl : IsClosed (WithTopology.ofTopology ⁻¹' s : Set (WithConstructibleTopology X)) :=
    WithConstructibleTopology.isClosed_iff.2
      (@isOpen_compl_iff _ _ (constructibleTopology X) |>.1 hclo.2)
  have := hcl.isCompact.image hcont
  rwa [Set.image_preimage_eq _ (WithTopology.ofTopology_surjective _)] at this

end Constructible

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- An immersion with constructible range into a quasi-compact quasi-separated scheme is
quasi-compact. -/
lemma quasiCompact_of_isImmersion_of_isConstructible {D X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (i : D ⟶ X) [IsImmersion i]
    (hi : IsConstructible (Set.range i)) : QuasiCompact i := by
  refine ⟨fun U hU hUc ↦ ?_⟩
  rw [i.isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range]
  exact ((hUc.isRetrocompact hU).isConstructible hU).inter hi |>.isCompact_of_compactSpace

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Gluing along a stratification.** On a quasi-compact quasi-separated scheme `X` with a
stratification `S`, a pro-étale sheaf of `Λ`-modules is of étale origin as soon as its pullbacks
to the strata are. -/
theorem essImage_comparisonUpperStar_of_stratification
    [Etale.HasCohomologyContinuity (ModuleCat.{u + 1} Λ)] {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (S : Scheme.Stratification X)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hS : ∀ k : Fin S.n, (comparisonUpperStar (ModuleCat.{u + 1} Λ) (S.domain k)).essImage
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).essImage F := by
  have (k : Fin S.n) : QuasiCompact (S.immersion k) :=
    quasiCompact_of_isImmersion_of_isConstructible _
      (by rw [S.range_immersion]; exact S.isConstructible_stratum k)
  have hsurj (x : X) : ∃ k, x ∈ Set.range (S.immersion k) := by
    have : x ∈ ⋃ k, S.stratum k := by rw [S.iUnion_stratum_eq_univ]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, by rwa [S.range_immersion]⟩
  refine essImage_comparisonUpperStar_of_detect S.immersion (fun H hH ↦ ?_) F hS
  exact (IsZero.iff_id_eq_zero H).2
    (eq_zero_of_forall_upperStar_map_eq_zero Λ S.immersion hsurj (𝟙 H) fun k ↦
      (hH k).eq_of_src _ _)

end AlgebraicGeometry.ProEtale
