/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-! # Internal Hom from open base change
The noetherian dévissage is in the second variable.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme
open _root_.AlgebraicGeometry.Etale.DerivedCategory
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
private theorem comparison_on_open_directImage
    {Z Z' V V' : Scheme.{u}} {gZ : Z' ⟶ Z} {j : V ⟶ Z}
    [IsOpenImmersion j] {j' : V' ⟶ Z'} [IsOpenImmersion j'] {gV : V' ⟶ V}
    (sqV : IsPullback gV j' j gZ)
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (D : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [ExactPairing D ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)]
    (N : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hbcN : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqV.toCommSq).app N))
    (hbcR : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqV.toCommSq).app
      ((RHom(V)[ModuleCat.{u + 1} Λ].obj
        (op ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))).obj N))) :
    IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N)) := by
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion Λ j
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion Λ j'
  let eA := (L((gZ)^*[ModuleCat.{u + 1} Λ])).mapIso
      (derivedHomRightDerivedLowerStarIso (ModuleCat.{u + 1} Λ) j K N) ≪≫
    asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqV.toCommSq).app _)
  let eB := (RHom(Z')[ModuleCat.{u + 1} Λ].obj
      (op ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K))).mapIso
      (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqV.toCommSq).app N)) ≪≫
    derivedHomRightDerivedLowerStarIso (ModuleCat.{u + 1} Λ) j' _ _
  have hρj' : IsIso (derivedHomUpperStarComparison _ j' ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N))) :=
    (isIso_derivedHomUpperStarComparison_iff_of_iso_right (ModuleCat.{u + 1} Λ) j'
    ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)
    (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqV.toCommSq).app N))).2
    (isIso_derivedHomUpperStarComparison_rightDerivedLowerStar _ j' _ _)
  have hρh : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) (j' ≫ gZ) K
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N)) := by
    rw [isIso_derivedHomUpperStarComparison_iff_comp _ gV j (j' ≫ gZ) sqV.w.symm]
    have := isIso_derivedHomUpperStarComparison_rightDerivedLowerStar _ j K N
    have := isIso_derivedHomUpperStarComparison_of_exactPairing _ gV D
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N))
    infer_instance
  rw [isIso_derivedHomUpperStarComparison_iff_comp _ j' gZ (j' ≫ gZ) rfl] at hρh
  have : IsIso ((L((j')^*[ModuleCat.{u + 1} Λ])).map
      (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N))) :=
    IsIso.of_isIso_comp_right _ (derivedHomUpperStarComparison _ j'
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((gZ)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj N)))
  exact (derivedUpperStarLowerStarAdjunction _ j').isIso_of_isIso_map_of_iso_rightAdjoint_obj
    eA eB _


/-- Open direct-image base change on all closed subschemes implies the internal-Hom
comparison for constructible finite-Tor first arguments and bounded-below second arguments.
Proof: noetherian induction; take a dense open where the first argument is dualizable,
use the localization triangle in the second argument, open base change on the open term,
and proper base change followed by induction on the closed term.
Source: the open-closed proof of the internal-Hom comparison, Bhatt--Scholze 6.3.16.
(blueprint: lem-weil-pbc-internal-hom-open-base-change). -/
theorem isIso_derivedHomUpperStarComparison_of_open_baseChange
    {X U : Scheme.{u}} [IsNoetherian X] (f : U ⟶ X)
    (hbc : ∀ {Z Z' V : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι]
      (gZ : Z' ⟶ Z) (i' : Z' ⟶ U), IsPullback gZ i' ι f →
      ∀ (j : V ⟶ Z) [IsOpenImmersion j],
      ∀ N : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      _root_.DerivedCategory.TStructure.t.plus N →
      IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback j gZ).toCommSq).app N))
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : _root_.DerivedCategory.TStructure.t.plus M) :
    IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) f K M) := by
  suffices key : ∀ C : TopologicalSpace.Closeds X, ∀ (Z : Scheme.{u}) (ι : Z ⟶ X)
      [IsClosedImmersion ι], Set.range ι.base ⊆ C → ∀ (Z' : Scheme.{u}) (gZ : Z' ⟶ Z)
      (i' : Z' ⟶ U), IsPullback gZ i' ι f →
      ∀ K M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z K →
      _root_.DerivedCategory.TStructure.t.plus M →
      IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) gZ K M) from
    key ⊤ X (𝟙 X) (by simp) U f (𝟙 U) IsPullback.of_id_snd K M hK hM
  intro C
  induction C using WellFoundedLT.induction with
  | _ C IH =>
  intro Z ι _ hι Z' gZ i' hsq K M hK hM
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace ι
  have : IsNoetherian Z := { __ := LocallyOfFiniteType.isLocallyNoetherian ι }
  rcases isEmpty_or_nonempty Z with hE | hE
  · have : IsEmpty Z' := ⟨fun z ↦ IsEmpty.false (gZ.base z)⟩
    exact IsZero.isIso
      (_root_.DerivedCategory.isZero_of_forall_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty ·) _)
      (_root_.DerivedCategory.isZero_of_forall_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty ·) _) _
  obtain ⟨V, hVd, hV⟩ := exists_dense_open_exactPairing Λ hK
  obtain ⟨D, hD, ⟨ep⟩⟩ := hV V le_rfl
  let i := V.closedComplement
  have hij : Set.range i.base = (Set.range V.ι.base)ᶜ := by simp [i]
  have sqW := (IsPullback.of_hasPullback gZ i).flip
  have sqV := IsPullback.of_hasPullback V.ι gZ
  have hN : _root_.DerivedCategory.TStructure.t.plus
      ((L((V.ι)^*[ModuleCat.{u + 1} Λ])).obj M) := by
    rcases hM with ⟨N, hN⟩
    have : M.IsGE N := hN
    have : (D((V.ι)^*[ModuleCat.{u + 1} Λ]).obj M).IsGE N :=
      ((V.ι)^*[ModuleCat.{u + 1} Λ]).isGE_mapDerivedCategory_obj M N
    exact ⟨N, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ V.ι).app M).symm N⟩
  have hbcN := hbc ι gZ i' hsq V.ι _ hN
  have hRH : _root_.DerivedCategory.TStructure.t.plus
      ((RHom(V)[ModuleCat.{u + 1} Λ].obj
        (op ((L((V.ι)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          ((L((V.ι)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
    obtain ⟨b, hb⟩ := hK.1.1.2
    obtain ⟨N, hN⟩ := hN
    have : K.IsLE b := hb
    have : ((L((V.ι)^*[ModuleCat.{u + 1} Λ])).obj K).IsLE b :=
      by
        have : (D((V.ι)^*[ModuleCat.{u + 1} Λ]).obj K).IsLE b :=
          ((V.ι)^*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj K b
        exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
          ((leftDerivedUpperStarIsoMapDerivedCategory _ V.ι).app K).symm b
    have : ((L((V.ι)^*[ModuleCat.{u + 1} Λ])).obj M).IsGE N := hN
    exact ⟨N-b, _root_.DerivedCategory.isGE_obj_of_adjunction
      (derivedTensorHomAdjunction _ _) _ b N⟩
  refine isIso_derivedHomUpperStarComparison_of_isIso_open_closed Λ hij sqV K M hbcN ?_
    (comparison_on_open_directImage Λ sqV K D _ hbcN
      (hbc ι gZ i' hsq V.ι _ hRH))
  refine isIso_derivedHomUpperStarComparison_rightDerivedLowerStar_of_isClosedImmersion
    Λ sqW K _ ?_
  have hsqW : IsPullback (pullback.snd gZ i) (pullback.fst gZ i ≫ i') (i ≫ ι) f :=
    sqW.paste_vert hsq
  let C' : TopologicalSpace.Closeds X :=
    ⟨Set.range (i ≫ ι).base, (i ≫ ι).isClosedEmbedding.isClosed_range⟩
  have hC : C' < C := by
    refine lt_of_le_of_ne (fun x hx ↦ hι ?_) fun heq ↦ ?_
    · obtain ⟨w, rfl⟩ := hx
      exact ⟨i.base w, rfl⟩
    · obtain ⟨v, hv⟩ := hVd.nonempty
      have hvC : ι.base v ∈ (C' : Set X) := heq ▸ hι ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := hvC
      have hwv : i.base w = v := ι.isClosedEmbedding.injective (by simpa using hw)
      have hvi : v ∈ Set.range i.base := ⟨w, hwv⟩
      rw [hij] at hvi
      exact hvi ⟨⟨v, hv⟩, rfl⟩
  exact IH C' hC _ (i ≫ ι) subset_rfl _ _ _ hsqW _ _
    (constructibleFiniteTor_leftDerivedUpperStar _ i hK)
    (plus_rightDerivedUpperShriek_obj Λ i M hM)
end AlgebraicGeometry.Etale
