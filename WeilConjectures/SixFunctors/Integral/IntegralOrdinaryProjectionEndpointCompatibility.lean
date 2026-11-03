/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
import all WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportFiniteMates
import all WeilConjectures.SixFunctors.PurCompactSupport.ProperScalarComposition
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullTensorCoefficientCoherence
import WeilConjectures.SixFunctors.Integral.IntegralOrdinaryProjectionEndpointNormalization
import all WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarProperProjectionPresentation
import all WeilConjectures.SixFunctors.Finite.FiniteProjectionOperationPresentation

/-! # Compatible endpoint comparisons for ordinary projection reduction

Source: the proper projection reduction paragraph of `sk-thm-sf-pf-adic` and
constant-scalar realization of the proper/open projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] ProEtale.projectionMapOfCompactification
attribute [local instance 100000] SheafOfModules.instAbelian
attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

private def curryTensorIso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C × C ⥤ C) (S : D × D ⥤ D)
    (e : T ⋙ F ≅ F.prod F ⋙ S) :
    (Functor.postcompose₂.obj F).obj (Functor.curry.obj T) ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (Functor.curry.obj S) :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun N ↦ e.app (M, N)) (by
      intro N N' h
      simpa using e.hom.naturality (Prod.mkHom (𝟙 M) h))) (by
        intro M M' h
        ext N
        simpa using e.hom.naturality (Prod.mkHom h (𝟙 N)))

attribute [local irreducible] sfIntrinsicDerivedEquivalence
  CategoryTheory.Functor.mapDerivedCategory sfIntrinsicModuleEquivalence
  PurCompactSupport.scalarPull PurCompactSupport.scalarTensor
  proEtaleCanonicalTensorComparison proEtaleRingDerivedAdjunction
  HasDerivedCategory.standard Functor.rightDerivedFunctor

attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian in
attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory in
private theorem properReductionArrow
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (n : ℕ)
    (bZ : ProEtaleTensorModel c.Z
      (proEtaleConstantRing c.Z (Padic.coefficientExtensionRing l E (n + 1))))
    (bY : ProEtaleTensorModel Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))
    (M : DerivedCategory (scalarReductionSource l E c.Z))
    (L : DerivedCategory (scalarReductionSource l E Y)) :
    let R := PurCompactSupport.completed l E
    let a := PurCompactSupport.reduction l E (n + 1) (Nat.succ_pos n)
    let data := (PurCompactSupport.projectionComparisons_existsUnique R c aX aZ aY
      (PurCompactSupport.completedPull_comp l E c.i c.g)).exists.choose
    Nonempty (Arrow.mk ((pbcDerivedExtend (a.map Y)).map
      ((((proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z)
        (R.pull c.g)).rightAdjointProjectionMap data.tensorPullback.hom).app M).app L)) ≅
      Arrow.mk (finiteScalarProperProjection (Padic.coefficientExtensionRing l E (n + 1))
        c.g bZ bY ((pbcDerivedExtend (a.map c.Z)).obj M)
          ((pbcDerivedExtend (a.map Y)).obj L))) := by
  let R := PurCompactSupport.completed l E
  let S := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.succ_pos n)
  let data := (PurCompactSupport.projectionComparisons_existsUnique R c aX aZ aY
    (PurCompactSupport.completedPull_comp l E c.i c.g)).exists.choose
  let adj := proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)
  let adj' := proEtaleRingDerivedAdjunction c.g (S.ring Y) (S.ring c.Z) (S.pull c.g)
  let CZ := pbcDerivedExtend (a.map c.Z)
  let CY := pbcDerivedExtend (a.map Y)
  let alpha := (PurCompactSupport.scalarPull a c.g).symm
  let tau := proEtaleCanonicalTensorComparison c.g
    (S.ring Y) (S.ring c.Z) (S.pull c.g) bY bZ
  let phi := curryTensorIso (PurCompactSupport.pull S c.g) bY.tensor bZ.tensor tau
  let tZ := curryTensorIso CZ aZ.tensor bZ.tensor
    (PurCompactSupport.scalarTensor (a.map c.Z) aZ bZ)
  let tY := curryTensorIso CY aY.tensor bY.tensor
    (PurCompactSupport.scalarTensor (a.map Y) aY bY)
  have hb (N : DerivedCategory (scalarReductionSource l E c.Z)) :
      IsIso ((mateEquiv adj adj' alpha.hom).natTrans.app N) := by
    change IsIso (((mateEquiv adj adj'
      (TwoSquare.mk _ _ _ _ (PurCompactSupport.scalarPull a c.g).inv)).natTrans).app N)
    rw [PurCompactSupport.properComparison_mate]
    exact quotient_proper_mate l E c.g n N
  let : IsIso (mateEquiv adj adj' alpha.hom).natTrans :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hb
  have hc : Adjunction.ComparisonCompatible alpha data.tensorPullback.hom phi.hom tZ tY := by
    intro P Q
    change CZ.map ((data.tensorPullback.hom.app P).app Q) ≫
        (PurCompactSupport.scalarTensor (a.map c.Z) aZ bZ).hom.app
          ((PurCompactSupport.pull R c.g).obj P, (PurCompactSupport.pull R c.g).obj Q) = _
    rw [data.tensorPullback_eq]
    have h := PurCompactSupport.scalarPull_tensor_coefficient_coherence
      a c.g aZ aY bZ bY P Q
    apply (cancel_epi ((PurCompactSupport.scalarPull a c.g).inv.app
      (aY.tensor.obj (P, Q)))).1
    simpa only [alpha, Iso.symm_hom, Iso.symm_inv, phi, tZ, tY, curryTensorIso,
      NatIso.ofComponents_hom_app, NatTrans.comp_app, Functor.curry_obj_obj_obj,
      Functor.curry_obj_map_app, Functor.curry_obj_obj_map, Functor.curry_map_app_app,
      Iso.app_hom, tau, Functor.map_id,
      ← bZ.tensor.map_comp, prod_comp, Prod.mkHom, Category.id_comp, Category.comp_id,
      Iso.inv_hom_id_app_assoc, Category.assoc] using h
  let e := projectionArrowIso adj adj' alpha data.tensorPullback.hom phi.hom tZ tY hc M L
  have hp : ((adj'.rightAdjointProjectionMap phi.hom).app (CZ.obj M)).app (CY.obj L) =
      finiteScalarProperProjection (Padic.coefficientExtensionRing l E (n + 1)) c.g
        bZ bY (CZ.obj M) (CY.obj L) := by
    unfold finiteScalarProperProjection
    rfl
  exact ⟨e ≪≫ eqToIso (congrArg Arrow.mk hp)⟩

attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian in
attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory in
private theorem compactificationProperArrow
    (R : PurCompactSupport.Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (aY : ProEtaleTensorModel Y (R.ring Y))
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (K : DerivedCategory (proEtaleRingModules X (R.ring X)))
    (L : DerivedCategory (proEtaleRingModules Y (R.ring Y))) :
    let data := (PurCompactSupport.projectionComparisons_existsUnique R c aX aZ aY hR).exists.choose
    Nonempty (Arrow.mk (((PurCompactSupport.projectionMap R c aX aZ aY hR).app K).app L) ≅
      Arrow.mk ((((proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z)
        (R.pull c.g)).rightAdjointProjectionMap data.tensorPullback.hom).app
          ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K)).app L)) := by
  let data := (PurCompactSupport.projectionComparisons_existsUnique R c aX aZ aY hR).exists.choose
  let p := (((proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z)
    (R.pull c.g)).rightAdjointProjectionMap data.tensorPullback.hom).app
      ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K)).app L
  let e := (PurCompactSupport.push R c.g).mapIso ((data.openProjection.app K).app L)
  exact ⟨(arrowPostIso p e).symm⟩

private theorem scalarArrowComparison
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F ≅ G) (q : Arrow C) :
    Nonempty (G.mapArrow.obj q ≅ F.mapArrow.obj q) :=
  ⟨(Arrow.isoOfNatIso e q).symm⟩

attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian in
attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory in
private theorem integralToFiniteProperArrow
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (n : ℕ)
    (bZ : ProEtaleTensorModel c.Z
      (proEtaleConstantRing c.Z (Padic.coefficientExtensionRing l E (n + 1))))
    (bY : ProEtaleTensorModel Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let R := PurCompactSupport.completed l E
    let a := PurCompactSupport.reduction l E (n + 1) (Nat.succ_pos n)
    Nonempty (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap R c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L)) ≅
      Arrow.mk (finiteScalarProperProjection A c.g bZ bY
        ((pbcDerivedExtend (a.map c.Z)).obj
          ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K))
        ((pbcDerivedExtend (a.map Y)).obj L))) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let R := PurCompactSupport.completed l E
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.succ_pos n)
  let CY := pbcDerivedExtend (a.map Y)
  let M := (PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K
  let p := ((PurCompactSupport.projectionMap R c aX aZ aY
    (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L
  obtain ⟨e₀⟩ := scalarArrowComparison (PurCompactSupport.finiteReductionIso l E Y n)
    (Arrow.mk p)
  obtain ⟨ec⟩ := compactificationProperArrow R c aX aZ aY
    (PurCompactSupport.completedPull_comp l E c.i c.g) K L
  let e₁ := CY.mapArrow.mapIso ec
  obtain ⟨e₂⟩ := properReductionArrow l E c aX aZ aY n bZ bY M L
  exact ⟨e₀ ≪≫ e₁ ≪≫ e₂⟩

attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian in
attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory in
private theorem finiteProperToCoordinateArrow
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (n : ℕ)
    (bZ : ProEtaleTensorModel c.Z
      (proEtaleConstantRing c.Z (Padic.coefficientExtensionRing l E (n + 1))))
    (bY : ProEtaleTensorModel Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let R := PurCompactSupport.completed l E
    let a := PurCompactSupport.reduction l E (n + 1) (Nat.succ_pos n)
    Nonempty (Arrow.mk (finiteScalarProperProjection A c.g bZ bY
        ((pbcDerivedExtend (a.map c.Z)).obj
          ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K))
        ((pbcDerivedExtend (a.map Y)).obj L)) ≅
      Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (projectionTensorCoordinateComponent (ModuleCat.{u + 1} (ULift.{u + 1} A)) c
          ((sfIntrinsicDerivedEquivalence X A).inverse.obj
            ((pbcDerivedExtend (a.map X)).obj K))
          ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
            ((pbcDerivedExtend (a.map Y)).obj L))))) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let R := PurCompactSupport.completed l E
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.succ_pos n)
  let CX := pbcDerivedExtend (a.map X)
  let CZ := pbcDerivedExtend (a.map c.Z)
  let CY := pbcDerivedExtend (a.map Y)
  let M := (PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K
  have hopen := PurCompactSupport.openComparison_isIso a c.i K
  let eJ := asIso ((PurCompactSupport.openComparison a c.i).app K) ≪≫
    finiteOpenRealizationIso l E n c.i (CX.obj K)
  obtain ⟨e₃⟩ := properToFixedCompactification A c bZ bY (CZ.obj M) (CX.obj K) (CY.obj L) eJ
  exact ⟨e₃⟩

attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian in
attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory in
/-- Scalar reduction and constant-scalar realization give compatible endpoint comparisons.
The endpoints are constructed together; arbitrary independent isomorphisms need not commute.

Source: the proper/open scalar comparison and constant-scalar realization in
`lem-sf-ordinary-projection-reduction-arrow-comparison`.
(blueprint: lem-sf-ordinary-projection-endpoint-compatibility-q2).

Proof: remove the invertible open factor from both compactification projection arrows.
Apply the scalar/tensor mate square to the proper projection. The positive coefficient
quotient is perfect, so its scalar direct-image mate is invertible. The tensor and
pullback comparisons are isomorphisms, and hence this square is an arrow isomorphism.
Transport the reduced open input using the exact open scalar comparison. Realize the
finite proper projection by finiteScalarProperProjection_presentation, then restore
its fixed-scalar open factor. Finally transport the two scalar inputs through
finiteReductionIso. Composing these arrow isomorphisms supplies compatible endpoints;
no statement about arbitrary independently chosen endpoints is used. -/
theorem integralOrdinaryProjection_endpointCompatibility
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    Nonempty (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L)) ≅
      Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L))))) := by
  let S := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  obtain ⟨bZ⟩ := PurCompactSupport.tensorModel_exists c.Z (S.ring c.Z)
  obtain ⟨bY⟩ := PurCompactSupport.tensorModel_exists Y (S.ring Y)
  obtain ⟨e₁⟩ := integralToFiniteProperArrow l E c aX aZ aY n bZ bY K L
  obtain ⟨e₂⟩ := finiteProperToCoordinateArrow l E c n bZ bY K L
  obtain ⟨e₃⟩ := integralOrdinaryProjection_reducedInputsNormalization l E c n K L
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩

end WeilConjectures
