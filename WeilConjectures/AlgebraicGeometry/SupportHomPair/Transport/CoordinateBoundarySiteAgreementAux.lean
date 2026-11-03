/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryModel.CoordinateBoundaryGeometricPullbackDefs
import WeilConjectures.AlgebraicGeometry.SupportHomPair.Transport.CoordinateBoundaryPullbackAux
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Iso

/-! # Coefficient adjustment for normalized supported-Hom transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.SupportHomPair

/-- The identity coefficient map adds no factor to supported cohomology.
Source: functoriality of homology (blueprint: aux-lem-pur-coordinate-boundary-site-agreement).
Proof: expand the coefficient map and use preservation of the identity. -/
theorem Transport.coefficientGroupMap_id
    {A : Type (u + 1)} [CommRing A] {S T : SupportHomPair A}
    {B : S.Site ⥤ T.Site} [B.IsContinuous S.topology T.topology]
    {L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.topology (ModuleCat.{u + 1} A)}
    {adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology}
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : Transport S T B L adj)
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (q : ℤ) :
    e.coefficientGroupMap (𝟙 (L.mapDerivedCategoryPlus.obj K)) q =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
        (e.derivedMap.app K) := by
  unfold Transport.coefficientGroupMap
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- A coefficient-adjusted group equality and normalized transport compatibility
imply the corresponding derived-Hom equality. Source: Milne, Example 9.5, and the
coefficient naturality clause of `supportedHom_pullback`.
Proof: replace the target class by its group-map expression. Apply naturality of
the target identification to the coefficient map, then the compatibility equation
for the unadjusted pullback. The resulting composite is the defined coefficient
Hom map. This needs no inverse-image preservation of injectives.
(blueprint: aux-lem-pur-coordinate-boundary-site-agreement) -/
theorem Transport.coefficientCompatible_of_compatible
    {A : Type (u + 1)} [CommRing A] {S T : SupportHomPair A}
    {B : S.Site ⥤ T.Site} [B.IsContinuous S.topology T.topology]
    {L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.topology (ModuleCat.{u + 1} A)}
    {adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology}
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : Transport S T B L adj) (chi : S.Identification) (chi' : T.Identification)
    {K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))}
    {K' : DerivedCategory.Plus (Sheaf T.topology (ModuleCat.{u + 1} A))}
    (b : L.mapDerivedCategoryPlus.obj K ⟶ K') (a : ℤ)
    (hc : e.Compatible chi chi' K a)
    (x : S.group K a) (y : T.group K' a)
    (hxy : e.coefficientGroupMap b a x = y) :
    e.CoefficientCompatible chi chi' b a x y := by
  refine ⟨hxy, ?_⟩
  erw [← hxy]
  change chi'.chi K' a
    ((Sheaf.supportHypercohomologyFunctor T.topology
      (ModuleCat.{u + 1} A) T.restriction a).map b
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).map
          (e.derivedMap.app K) x)) = _
  erw [chi'.naturality]
  exact congrArg (fun f ↦ f ≫ (DerivedCategory.Plus.ι.map b)⟦a⟧') (hc x)

end AlgebraicGeometry.SupportHomPair

namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] ProEtale.comparisonLowerStar
  Functor.sheafPushforwardContinuous coordinateEtaleInput coordinateProInput
  Sheaf.supportedSectionsFunctor DerivedCategory.Plus.homologyFunctor
  MorphismProperty Functor.mapDerivedCategoryPlus
  Scheme.toProEt Scheme.Etale Scheme.ProEt
  Scheme.instCategoryEtale Scheme.instCategoryProEt
  ProEtale.supportComparisonHypercohomology MorphismProperty.Comma.instCategory

private theorem siteTransport_openDerivedMap_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (v : siteSupportHomTransport P i) :
    let := Scheme.isContinuous_toProEt X
    v.openDerivedMap =
      ProEtale.finiteComparisonSection X P.Coefficient
        (Scheme.Etale.mk i.openComplement.ι) := by
  let := Scheme.isContinuous_toProEt X
  have hm : v.complementMap (hB := Scheme.isContinuous_toProEt X) =
      𝟙 (Scheme.ProEt.mk i.openComplement.ι) := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono i.openComplement.ι).1
    exact (MorphismProperty.Over.w _).trans (Category.id_comp _).symm
  have hu : (Functor.rightUnitor _).hom ≫ v.openUnit =
      ProEtale.finiteComparisonSectionUnit X P.Coefficient
        (Scheme.Etale.mk i.openComplement.ι) := by
    ext F
    simp only [NatTrans.comp_app, Functor.rightUnitor_hom_app,
      SupportHomPair.Transport.openUnit]
    erw [hm, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  unfold SupportHomPair.Transport.openDerivedMap ProEtale.finiteComparisonSection
  rw [hu]

set_option maxHeartbeats 1600000 in
-- The four derived section functors elaborate large comparison structures.
/-- The coefficient-adjusted pullback square commutes on supported cohomology.
Source: the support comparison square and the definition of the pro-etale coefficient map.
Proof: take cohomology of the coherent derived square, cancel the inverse comparison
in the pro-etale coefficient map, then use naturality of the target site map with
respect to the etale coefficient map.
(blueprint: aux-lem-pur-coordinate-boundary-site-agreement). -/
theorem coordinate_boundary_coefficient_square (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (f : X' ⟶ X)
    (e : etaleSupportHomTransport P i i' f)
    (p : proEtaleSupportHomTransport P i i' f)
    (v : siteSupportHomTransport P i) (v' : siteSupportHomTransport P i')
    (hc : SupportHomSquareCoherent P i i' f e p v v') (q : ℤ) :
    v.coefficientGroupMap (hB := Scheme.isContinuous_toProEt X)
        (𝟙 (P.coordinateProInput h X)) q ≫
      p.coefficientGroupMap (hB := Scheme.ProEt.isContinuous_overPullback f)
        (P.coordinateProCoefficientPullback h f) q =
    e.coefficientGroupMap (hB := Etale.isContinuous_overPullback f)
        (P.coordinateEtaleCoefficientPullback h f) q ≫
      v'.coefficientGroupMap (hB := Scheme.isContinuous_toProEt X')
        (𝟙 (P.coordinateProInput h X')) q := by
  let K := P.coordinateEtaleInput h X
  let K' := P.coordinateEtaleInput h X'
  let RE := (etaleSupportHomPair P i').sections.rightDerivedFunctorPlus
  let RP := (proEtaleSupportHomPair P i').sections.rightDerivedFunctorPlus
  let V' := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategoryPlus
  let b := P.coordinateEtaleCoefficientPullback h f
  have hn := (v'.derivedMap (hB := Scheme.isContinuous_toProEt X')).naturality b
  have hd : (v.derivedMap (hB := Scheme.isContinuous_toProEt X)).app K ≫
      (p.derivedMap (hB := Scheme.ProEt.isContinuous_overPullback f)).app
        (P.coordinateProInput h X) ≫ RP.map (P.coordinateProCoefficientPullback h f) =
    (e.derivedMap (hB := Etale.isContinuous_overPullback f)).app K ≫
      RE.map b ≫ (v'.derivedMap (hB := Scheme.isContinuous_toProEt X')).app K' := by
    erw [← Category.assoc]
    with_unfolding_all
      change (v.derivedMap.app K ≫ p.derivedMap.app
      ((ProEtale.comparisonUpperStar (ModuleCat P.Coefficient) X).mapDerivedCategoryPlus.obj K))
        ≫ RP.map (P.coordinateProCoefficientPullback h f) = _
    with_unfolding_all
      erw [hc.1 K]
    simp only [coordinateProCoefficientPullback, CategoryTheory.Functor.map_comp,
      Category.assoc]
    erw [← RP.map_comp_assoc, Iso.hom_inv_id_app, RP.map_id, Category.id_comp]
    exact congrArg (fun z ↦ (e.derivedMap
      (hB := Etale.isContinuous_overPullback f)).app K ≫ z) hn.symm
  erw [v.coefficientGroupMap_id, v'.coefficientGroupMap_id]
  have hh := congrArg (DerivedCategory.Plus.homologyFunctor
    (ModuleCat.{u + 1} P.Coefficient) q).map hd
  with_unfolding_all
    simpa only [SupportHomPair.Transport.coefficientGroupMap,
    K, K', RE, RP, b, Sheaf.supportHypercohomologyFunctor,
    CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc] using hh

end WeilConjectures.PurityFiniteSetting
