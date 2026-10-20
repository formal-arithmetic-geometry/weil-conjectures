/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor

import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicLisseFixed
import Sheaf.AlgebraicGeometry.EtaleAffineLinePullbackFull
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! # Lifting affine-line endomorphisms through the ordinary etale comparison -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every endomorphism of a finite locally constant module on the affine line is induced
from the base. This is the full-faithfulness/lifting part of the connected-fibre argument.
Source: Stacks Project, Tags 0A3H and 099Y.
(blueprint: new-lem-pur-a1-pullback-lift).

Proof: use the coefficient bridge to obtain a fixed-module lisse sheaf, then its etale
origin G. Etale affine-line pullback is full by objectwise section invariance. Comparison
is full by its ordinary unit isomorphism, and intrinsic realization is an equivalence.
The canonical inverse-image comparison and realization unit identify their composite
with intrinsic affine-line pullback after intrinsic comparison. Thus that composite is
full. Conjugate h by the pullback of the origin isomorphism, lift through the full
composite, and conjugate the lifted comparison map back on the base. The functor map
laws and inverse identities verify that the resulting b pulls back to h. -/
theorem proEtale_a1_pullback_lift (S : Scheme.{u})
    (Λ : Type u) [CommRing Λ] [Finite Λ]
    (M : proEtaleRingModules S (proEtaleConstantRing S Λ))
    (hM : IsLocallyConstantProEtaleModuleSheaf S Λ M)
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ S),
      Finite ((finiteCoefficientModuleStalkFunctor y Λ).obj M))
    (h : (sfIntrinsicPullback Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj M ⟶
      (sfIntrinsicPullback Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj M) :
    ∃ b : M ⟶ M,
      (sfIntrinsicPullback Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).map b = h := by
  let D := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)
  let p := AffineSpace (ULift.{u} (Fin 1)) S ↘ S
  let X := AffineSpace (ULift.{u} (Fin 1)) S
  let E := sfIntrinsicModuleEquivalence S Λ
  let E' := sfIntrinsicModuleEquivalence X Λ
  let C := ProEtale.comparisonUpperStar D S ⋙ E.functor
  let L := Etale.upperStar D p ⋙ ProEtale.comparisonUpperStar D X ⋙ E'.functor
  let : (Etale.upperStar D p).Full := etale_a1_pullback_full S _
  let c : L ≅ C ⋙ sfIntrinsicPullback Λ p :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ProEtale.comparisonUpperStarCompUpperStarIso D p).symm E'.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (ProEtale.comparisonUpperStar D S)
        ((Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight E.unitIso _ ≪≫
          Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm
  let : (C ⋙ sfIntrinsicPullback Λ p).Full := Functor.Full.of_iso c
  obtain ⟨G, _, ⟨e⟩⟩ := (proEtale_lisse_origin S (ULift.{u + 1, u} Λ)).2
    (E.inverse.obj M) (proEtale_intrinsic_lisse_fixed S Λ M hM hfinite)
  let v : C.obj G ≅ M := E.functor.mapIso e ≪≫ E.counitIso.app M
  let w := (sfIntrinsicPullback Λ p).mapIso v
  obtain ⟨b, hb⟩ := (C ⋙ sfIntrinsicPullback Λ p).map_surjective
    (w.hom ≫ h ≫ w.inv)
  refine ⟨v.inv ≫ C.map b ≫ v.hom, ?_⟩
  simp only [CategoryTheory.Functor.map_comp]
  change w.inv ≫ (C ⋙ sfIntrinsicPullback Λ p).map b ≫ w.hom = h
  rw [hb]
  simp

end AlgebraicGeometry.Scheme
