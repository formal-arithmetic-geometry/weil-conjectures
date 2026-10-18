/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Acyclic open extensions in an etale compactification

Source: Stacks Project, More on Etale Cohomology, Tag 0GKM.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Open extension in a compactification of an etale map is acyclic for the proper
projection. Source: Stacks Project, More on Etale Cohomology, Tag 0GKM.
(blueprint: lem-f7-etale-compactification-acyclic).

Proof: Test each positive derived image on all geometric inverse images. Exact inverse
image moves homology through that pullback, and proper base change identifies the result
with compact support on the etale geometric fibre. A quasi-compact quasi-finite morphism
to a field is finite (`IsFinite.of_locallyQuasiFinite` over the Artinian base). Thus the
fibre map is proper; the open immersion of its compactification has closed range and
its extension by zero is ordinary direct image. Exactness of that clopen direct image,
composition of derived direct images, and exactness of finite direct image identify the
fibre's compact support with the degreewise finite direct image. It takes a sheaf in
degree zero to a complex concentrated in degree zero. All positive homology therefore
vanishes. Conservative geometric inverse images give the asserted acyclicity. -/
theorem etaleCompactification_acyclic
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    (c : Compactification u) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightAcyclic
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj F) := by
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
  let P := lowerStar (ModuleCat.{u + 1} A) c.g
  let K := (DerivedCategory.singleFunctor _ 0).obj F
  intro n
  apply isZero_of_forall_isZero_upperStar_algClosurePoint A
  intro x
  let s := X.algClosurePoint x
  let T := upperStar (ModuleCat.{u + 1} A) s
  let t := pullback.snd s u
  let v := pullback.fst s u
  have : IsFinite v := .of_locallyQuasiFinite v
  let c' := c.ofIsPullback (IsPullback.of_hasPullback s u).flip
  have hproper := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite (IsPullback.of_hasPullback c.g s)
  have hbc := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback s u).flip c
  let e₁ : P.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj (J.obj F)) ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K :=
    P.rightDerivedFunctor.mapIso ((J.mapDerivedCategorySingleFunctor 0).app F).symm
  let e₂ := (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) s).symm.app _ ≪≫
    (asIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback s u).flip c)).app K ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c').mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) t).app K)
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} A) c'.i (c'.isClopen_range_openImmersion inferInstance).isClosed
  let ι := asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c'.i)
  have : PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) c'.i) :=
    preservesFiniteColimits_of_natIso ι
  let E := lowerStar (ModuleCat.{u + 1} A) v
  have : PreservesFiniteColimits E := inferInstance
  let e₃ := (Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso ι) _ ≪≫
    Functor.isoWhiskerRight
      (lowerStar (ModuleCat.{u + 1} A) c'.i).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    rightDerivedLowerStarComp (ModuleCat.{u + 1} A) c'.i c'.g ≪≫
    rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) c'.comm.symm ≪≫
    E.rightDerivedFunctorIsoMapDerivedCategory).app
      ((upperStar (ModuleCat.{u + 1} A) t).mapDerivedCategory.obj K)
  let T' := upperStar (ModuleCat.{u + 1} A) t
  have : K.IsLE 0 := inferInstanceAs
    (((DerivedCategory.singleFunctor _ 0).obj F).IsLE 0)
  have : (T'.mapDerivedCategory.obj K).IsLE 0 := T'.isLE_mapDerivedCategory_obj K 0
  have : (E.mapDerivedCategory.obj (T'.mapDerivedCategory.obj K)).IsLE 0 :=
    E.isLE_mapDerivedCategory_obj _ 0
  let q : ℤ := (n + 1 : ℕ)
  have hz := DerivedCategory.isZero_of_isLE
    (E.mapDerivedCategory.obj (T'.mapDerivedCategory.obj K)) 0 q (by dsimp [q]; omega)
  let e₀ := T.mapIso
    (P.homologyRightDerivedFunctorObjSingleFunctorIso (J.obj F) (n + 1)).symm
  let e₄ := (T.mapDerivedCategoryHomologyFunctorIso q).app
    (P.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj (J.obj F)))
  let e₅ := (DerivedCategory.homologyFunctor _ q).mapIso
    (T.mapDerivedCategory.mapIso e₁ ≪≫ e₂ ≪≫ e₃)
  exact hz.of_iso (e₀ ≪≫ e₄ ≪≫ e₅)

end AlgebraicGeometry.Etale
