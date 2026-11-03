/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude

import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.InternalHomOpenBaseChange
import WeilConjectures.AlgebraicGeometry.IndEtaleAffineNeighborhoods
import WeilConjectures.AlgebraicGeometry.IndEtaleQcqsDirectImageBaseChange
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus

/-! # Isomorphism core for affine ind-etale internal-Hom comparison

Source: Bhatt--Scholze, Lemma 6.3.16, pp. 47--48
(blueprint: lem-weil-pbc-ind-etale-internal-hom-isomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry
open Scheme
namespace Etale

/-- The canonical evaluation-transpose comparison is invertible for affine ind-etale
pullback. Convert finite-value constructibility to the equivalent source convention and
apply the noetherian open-base-change criterion. Every closed base change of the given
morphism is affine pro-etale and has affine ind-etale neighborhoods. The existing D+
direct-image base-change theorem applies there, and the canonical D+/D compatibility
identifies it with the actual unbounded exchange required by the criterion.

Source: Bhatt--Scholze, Lemma 6.3.16, pp. 47--48, small-etale analogue.
(blueprint: lem-weil-pbc-ind-etale-internal-hom-isomorphism). -/
theorem isIso_derivedHomUpperStarComparison_of_proAffineEtale
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U : Scheme.{u}} [IsNoetherian X] [IsNoetherian U]
    (f : U ⟶ X) [IsAffineHom f]
    (hf : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) f)
    (K M : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hKtor : DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) X K)
    (hM : ∃ N : ℤ, M.IsGE N)
    [UpperStarPreservesFlat (ModuleCat.{u + 1} A)] :
    IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) f K M) := by
  have hb : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
    rcases hK with ⟨hc, a, b, hab, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦ ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun i hi ↦ hz i (.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun i hi ↦ hz i (.inr hi)
    · exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  apply isIso_derivedHomUpperStarComparison_of_open_baseChange A f ?_ K M
    ⟨hb, hKtor⟩ hM
  intro Z Z' V ι hι gZ i' sqZ j hj N hN
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace ι
  have : IsNoetherian Z := { __ := LocallyOfFiniteType.isLocallyNoetherian ι }
  have : IsAffineHom gZ := MorphismProperty.of_isPullback sqZ.flip ‹IsAffineHom f›
  have hgZ : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) gZ :=
    MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback sqZ.flip hf
  exact (isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback j gZ).toCommSq ⟨N, hN⟩).2
      (isIso_derivedBaseChangeMapPlus_of_affine_locally_indEtale A j gZ
        (affine_indEtale_neighborhoods gZ hgZ) ⟨N, hN⟩)

end Etale
end AlgebraicGeometry
