/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Paper.DerivedLocalIsomorphismSourceEvaluation
public import Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import Mathlib.CategoryTheory.Adjunction.Comma

/-! # Normalization transport for local derived Isom sheaves

Source: Stacks Project, Tags 06YY, 098K, 09BV and 0F63.
(blueprint: lem-weil-pbc-normalized-derived-isomorphism-transport).

Universal normalization arrows define reduction on the slice Isom sheaves. Canonical
localization and coefficient comparisons transport its evaluation square to source sites.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t u₀ u₁ u₂ u₃ u₄ v₀ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
set_option backward.isDefEq.respectTransparency false in
theorem comparison_coefficient_mate_eq (q : R →+* S)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    (normalizationPullbackIso X.smallEtaleTopology (toProEt X) (ProEt.topology X) q).hom.app M =
      comparisonRestrictScalarsMap X R q M := by
  simp only [normalizationPullbackIso, asIso_hom, normalizationPullbackMate,
    mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, comparisonRestrictScalarsMap,
    Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem comparison_coefficient_derived_eq (q : R →+* S) :
    localIsomorphismComparisonCoefficients (X := X) q =
      comparisonRestrictScalarsIso X R q := by
  have h : normalizationPullbackIso X.smallEtaleTopology (toProEt X)
      (ProEt.topology X) q = comparisonRestrictScalarsSheafIso X R q := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    exact comparison_coefficient_mate_eq X q M
  unfold localIsomorphismComparisonCoefficients comparisonRestrictScalarsIso
  rw [h]

variable (U : X.ProEt)
set_option backward.isDefEq.respectTransparency false in
theorem proet_coefficient_mate_eq (q : R →+* S)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q).hom.app M =
      ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom).homEquiv _ _).symm
        ((sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom).unit.app M)) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  simp only [normalizationPullbackIso, asIso_hom, normalizationPullbackMate,
    mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem proet_localization_coefficient_mate (q : R →+* S)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q).hom.app M ≫
        (sheafCompose (ProEt.topology U.left)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((ProEtale.upperStarIsoLocalizationRestriction
            (ModuleCat.{u + 1} S) U.hom U.prop).hom.app M) =
      (ProEtale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} R) U.hom U.prop).hom.app
          ((sheafCompose (ProEt.topology X)
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let aR := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) U.hom
  let aS := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) U.hom
  let bR := ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} R) U.hom U.prop
  let bS := ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} S) U.hom U.prop
  apply (aR.homEquiv _ _).injective
  rw [aR.homEquiv_naturality_right, proet_coefficient_mate_eq,
    Equiv.apply_symm_apply]
  change _ = aR.homEquiv _ _ ((aR.leftAdjointUniq bR).hom.app _)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hs := Adjunction.homEquiv_leftAdjointUniq_hom_app aS bS M
  rw [Adjunction.homEquiv_unit] at hs
  change
    (sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map (aS.unit.app M) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} R) U.hom).map
        ((sheafCompose (ProEt.topology U.left)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
          ((aS.leftAdjointUniq bS).hom.app M)) = _
  change (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      (aS.unit.app M) ≫
    (sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).map
      ((ProEtale.lowerStar (ModuleCat.{u + 1} S) U.hom).map
        ((aS.leftAdjointUniq bS).hom.app M)) = _
  rw [← CategoryTheory.Functor.map_comp, hs]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

noncomputable def proetSliceEquivalenceCoefficients (U : X.ProEt) (q : R →+* S) :
    Sheaf.restrictScalars ((ProEt.topology X).over U) q ⋙
        (proetSliceEquivalence X R U).functor ≅
      (proetSliceEquivalence X S U).functor ⋙
        Sheaf.restrictScalars (ProEt.topology U.left) q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

set_option backward.isDefEq.respectTransparency false in
theorem proetSliceCoefficients_pasting (U : X.ProEt) (q : R →+* S)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) :
    let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q).hom.app M ≫
      (Sheaf.restrictScalars (ProEt.topology U.left) q).map
        ((proetSliceRestrictionIso X S U).inv.app M) =
    (proetSliceRestrictionIso X R U).inv.app
      ((Sheaf.restrictScalars (ProEt.topology X) q).obj M) ≫
      (proetSliceEquivalence X R U).functor.map
        ((sliceRestrictScalarsSheafIso (ProEt.topology X) R q U).inv.app M) ≫
      (proetSliceEquivalenceCoefficients X U q).hom.app
        (((ProEt.topology X).overPullback (ModuleCat.{u + 1} S) U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  have h := proet_localization_coefficient_mate X U q M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  have hh := congrArg (fun k ↦ k.hom.app V) h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun k ↦ k x) hh


noncomputable def proetDerivedSliceEquivalenceCoefficients (U : X.ProEt) (q : R →+* S) :
    Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) q ⋙
        (proetSliceEquivalence X R U).functor.mapDerivedCategory ≅
      (proetSliceEquivalence X S U).functor.mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (ProEt.topology U.left) q :=
  Functor.mapDerivedCategorySquareIso (proetSliceEquivalenceCoefficients X U q)

set_option backward.isDefEq.respectTransparency false in
theorem proetDerivedSliceCoefficients_pasting (U : X.ProEt) (q : R →+* S)
    (M : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))) :
    (localIsomorphismProEtaleCoefficients U.hom q).hom.app M ≫
      (normalizationRestrict (ProEt.topology U.left) q).map
        ((proetDerivedSliceRestrictionIso X S U).inv.app M) =
    (proetDerivedSliceRestrictionIso X R U).inv.app
      ((normalizationRestrict (ProEt.topology X) q).obj M) ≫
      (proetSliceEquivalence X R U).functor.mapDerivedCategory.map
        ((sliceRestrictScalarsIso (ProEt.topology X) R q U).inv.app M) ≫
      (proetDerivedSliceEquivalenceCoefficients X U q).hom.app
        ((derivedSliceRestriction (ProEt.topology X) S U).obj M) := by
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.WeaklyEtale ⊤ U.hom) (ModuleCat.{u + 1} S)
      (ProEt.topology X) (ProEt.topology U.left)).Additive := by
    change (ProEtale.upperStar (ModuleCat.{u + 1} S) U.hom).Additive
    infer_instance
  let : (Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback
      @AlgebraicGeometry.WeaklyEtale ⊤ U.hom) (ModuleCat.{u + 1} R)
      (ProEt.topology X) (ProEt.topology U.left)).Additive := by
    change (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom).Additive
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} R) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteLimits (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} R) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteColimits (ProEtale.upperStar (ModuleCat.{u + 1} R) U.hom)
    infer_instance
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} S) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteLimits (ProEtale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  let : PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @AlgebraicGeometry.WeaklyEtale ⊤ U.hom)
      (ModuleCat.{u + 1} S) (ProEt.topology X) (ProEt.topology U.left)) := by
    change PreservesFiniteColimits (ProEtale.upperStar (ModuleCat.{u + 1} S) U.hom)
    infer_instance
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (sliceRestrictScalarsSheafIso (ProEt.topology X) R q U).symm
    (proetSliceEquivalenceCoefficients X U q)
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom)
      (ProEt.topology U.left) q)
    (proetSliceRestrictionIso X R U).symm
    (proetSliceRestrictionIso X S U).symm
    (proetSliceCoefficients_pasting X U q) M
  simp only [localIsomorphismProEtaleCoefficients, proetDerivedSliceRestrictionIso,
    proetDerivedSliceEquivalenceCoefficients, sliceRestrictScalarsIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc] at h ⊢
  convert! h using 1

end AlgebraicGeometry.Scheme

namespace CategoryTheory
section TransportSquare
variable {H S P Q : Type*} [Category H] [Category S] [Category P] [Category Q]
    (ER : H ⥤ P) (ES : S ⥤ Q) (RS : S ⥤ H) (RP : Q ⥤ P)
    (c : RS ⋙ ER ≅ ES ⋙ RP)
    {A D : H} {A' D' : S} {A₀ D₀ : P} {A₁ D₁ : Q}
    (δA : ER.obj A ≅ A₀) (δD : ER.obj D ≅ D₀)
    (εA : ES.obj A' ≅ A₁) (εD : ES.obj D' ≅ D₁)
    (dA : A ⟶ RS.obj A') (dD : D ⟶ RS.obj D')
    (dA₀ : A₀ ⟶ RP.obj A₁) (dD₀ : D₀ ⟶ RP.obj D₁)
    (hA : δA.hom ≫ dA₀ = ER.map dA ≫ c.hom.app A' ≫ RP.map εA.hom)
    (hD : δD.hom ≫ dD₀ = ER.map dD ≫ c.hom.app D' ≫ RP.map εD.hom)
include hA hD in
theorem normalized_square_transport
    (e : A ≅ D) (e' : A' ≅ D')
    (he : e.hom ≫ dD = dA ≫ RS.map e'.hom) :
    (δA.symm ≪≫ ER.mapIso e ≪≫ δD).hom ≫ dD₀ =
      dA₀ ≫ RP.map (εA.symm ≪≫ ES.mapIso e' ≪≫ εD).hom := by
  apply (cancel_epi δA.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  rw [hD, reassoc_of% hA]
  simp only [← RP.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [← ER.map_comp_assoc, he, ER.map_comp, Category.assoc]
  have hn := c.hom.naturality e'.hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

end TransportSquare
end CategoryTheory

namespace CategoryTheory.StructuredArrow
variable {C : Type u} [Category.{v} C] {D : Type t} [Category.{w} D]
  {R : C ⥤ D} {A A' : D} {K K' : C}
  {d : A ⟶ R.obj K} {d' : A' ⟶ R.obj K'}
noncomputable def universalIso
    (h : IsUniversal (mk d)) (h' : IsUniversal (mk d')) (e : A ≅ A') : K ≅ K' where
  hom := h.desc (mk (e.hom ≫ d'))
  inv := h'.desc (mk (e.inv ≫ d))
  hom_inv_id := by
    apply h.hom_ext
    rw [Functor.map_comp, ← Category.assoc, h.fac]
    change (e.hom ≫ d') ≫ R.map (h'.desc (mk (e.inv ≫ d))) = d ≫ R.map (𝟙 K)
    rw [Category.assoc]
    have hf : d' ≫ R.map (h'.desc (mk (e.inv ≫ d))) = e.inv ≫ d := h'.fac _
    rw [hf]
    change e.hom ≫ e.inv ≫ d = d ≫ R.map (𝟙 K)
    rw [← Category.assoc, e.hom_inv_id]
    simp
  inv_hom_id := by
    apply h'.hom_ext
    rw [Functor.map_comp, ← Category.assoc, h'.fac]
    change (e.inv ≫ d) ≫ R.map (h.desc (mk (e.hom ≫ d'))) = d' ≫ R.map (𝟙 K')
    rw [Category.assoc]
    have hf : d ≫ R.map (h.desc (mk (e.hom ≫ d'))) = e.hom ≫ d' := h.fac _
    rw [hf]
    change e.inv ≫ e.hom ≫ d' = d' ≫ R.map (𝟙 K')
    rw [← Category.assoc, e.inv_hom_id]
    simp
@[reassoc]
theorem universalIso_fac
    (h : IsUniversal (mk d)) (h' : IsUniversal (mk d')) (e : A ≅ A') :
    d ≫ R.map (universalIso h h' e).hom = e.hom ≫ d' :=
  h.fac _

end CategoryTheory.StructuredArrow

namespace CategoryTheory
section
variable {C D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
  {A K : C} {A' K' : D} (tA : L.obj A ≅ A') (tK : L.obj K ≅ K')

theorem adjunct_conjugation_square (e : A ≅ K) :
    e.hom ≫ (a.unit.app K ≫ R.map tK.hom) =
      (a.unit.app A ≫ R.map tA.hom) ≫
        R.map (tA.symm ≪≫ L.mapIso e ≪≫ tK).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]
  exact (reassoc_of% (a.unit.naturality e.hom)) (R.map tK.hom)

end
end CategoryTheory

namespace AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite
variable (X : Scheme.{u}) (B B' : Type (u + 1)) [CommRing B] [CommRing B']
  (φ : B →+* B')
  (T : DerivedLocalFunctor X.smallEtaleTopology B B')
  (S : DerivedLocalFunctor (ProEt.topology X) B B')
  (c : derivedComparison X B ⋙ S.globalFunctor ≅
    T.globalFunctor ⋙ derivedComparison X B')
  (aT : T.globalFunctor ⊣ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  (aS : S.globalFunctor ⊣ Sheaf.derivedRestrictScalars (ProEt.topology X) φ)
  (aSL : ∀ U : X.ProEt, S.localFunctor U ⊣
    Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ)
  (hS : ∀ (A : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)))
    (U : X.ProEt),
    (aSL U).unit.app ((derivedSliceRestriction (ProEt.topology X) B U).obj A) ≫
        (Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ).map
          ((S.restrictionIso U).hom.app A) ≫
        (sliceRestrictScalarsIso (ProEt.topology X) B φ U).hom.app
          (S.globalFunctor.obj A) =
      (derivedSliceRestriction (ProEt.topology X) B U).map (aS.unit.app A))
  (hc : ∀ A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
    aS.unit.app ((derivedComparison X B).obj A) ≫
        (Sheaf.derivedRestrictScalars (ProEt.topology X) φ).map (c.hom.app A) =
      (derivedComparison X B).map (aT.unit.app A) ≫
        (comparisonRestrictScalarsIso X B φ).hom.app (T.globalFunctor.obj A))

include hS hc in
set_option backward.isDefEq.respectTransparency false in
theorem scalarEvaluationTransport_unit
    (A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (U : X.ProEt) :
    (aSL U).unit.app
        ((derivedSliceRestriction (ProEt.topology X) B U).obj
          ((derivedComparison X B).obj A)) ≫
      (Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ).map
        (scalarEvaluationTransport T S c A U).hom ≫
      (sliceRestrictScalarsIso (ProEt.topology X) B φ U).hom.app
        ((derivedComparison X B').obj (T.globalFunctor.obj A)) =
    (derivedSliceRestriction (ProEt.topology X) B U).map
      ((derivedComparison X B).map (aT.unit.app A) ≫
        (comparisonRestrictScalarsIso X B φ).hom.app (T.globalFunctor.obj A)) := by
  simp only [scalarEvaluationTransport, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.app_hom]
  have hn := (sliceRestrictScalarsIso (ProEt.topology X) B φ U).hom.naturality
    (c.hom.app A)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]
  rw [reassoc_of% hS, ← Functor.map_comp, hc, Functor.map_comp]


noncomputable def sliceComparisonNormalization
    {A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {A' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B'))}
    (d : A ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj A')
    (U : X.ProEt) :=
  (derivedSliceRestriction (ProEt.topology X) B U).map
    ((derivedComparison X B).map d ≫
      (comparisonRestrictScalarsIso X B φ).hom.app A') ≫
    (sliceRestrictScalarsIso (ProEt.topology X) B φ U).inv.app
      ((derivedComparison X B').obj A')

include hS hc in
set_option backward.isDefEq.respectTransparency false in
theorem sliceComparisonNormalization_unit
    (A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (A' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B')))
    (d : A ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj A')
    (α : T.globalFunctor.obj A ≅ A')
    (hα : aT.unit.app A ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map α.hom = d)
    (U : X.ProEt) :
    sliceComparisonNormalization X B B' φ d U =
      (aSL U).unit.app
        ((derivedSliceRestriction (ProEt.topology X) B U).obj
          ((derivedComparison X B).obj A)) ≫
      (Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ).map
        (scalarEvaluationTransport T S c A U ≪≫
          (derivedSliceRestriction (ProEt.topology X) B' U).mapIso
            ((derivedComparison X B').mapIso α)).hom := by
  apply (cancel_mono ((sliceRestrictScalarsIso (ProEt.topology X) B φ U).hom.app
    ((derivedComparison X B').obj A'))).mp
  simp only [sliceComparisonNormalization, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  have hn := (sliceRestrictScalarsIso (ProEt.topology X) B φ U).hom.naturality
    ((derivedComparison X B').map α.hom)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [Category.comp_id]
  rw [hn, reassoc_of% scalarEvaluationTransport_unit X B B' φ T S c aT aS aSL hS hc A U]
  simp only [← Functor.map_comp]
  congr 1
  have hn' := (comparisonRestrictScalarsIso X B φ).hom.naturality α.hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn'
  rw [Category.assoc, ← hn', ← Category.assoc, ← Functor.map_comp, hα]


noncomputable def scalarConjugationReduction
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    {A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B'))}
    (αA : T.globalFunctor.obj A ≅ A') (αD : T.globalFunctor.obj D ≅ D') :=
  T.isoSheafMap A D ≫ derivedLocalIsoSheafMap αA.symm αD

set_option backward.isDefEq.respectTransparency false in
theorem scalarConjugationReduction_evaluation
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    {A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B'))}
    (αA : T.globalFunctor.obj A ≅ A') (αD : T.globalFunctor.obj D ≅ D')
    (U : X.ProEt) [IsAffine U.left]
    (hw : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (he : ∀ s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U),
      derivedIsoEvaluation X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) U hw
          (((comparisonSetUpperStar X).map (T.isoSheafMap A D)).hom.app (op U) s) =
        (scalarEvaluationTransport T S c A U).symm ≪≫
          (S.localFunctor U).mapIso (derivedIsoEvaluation X B A D U hw s) ≪≫
            scalarEvaluationTransport T S c D U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    derivedIsoEvaluation X B' A' D' U hw
      (((comparisonSetUpperStar X).map
        (scalarConjugationReduction X B B' T A D αA αD)).hom.app (op U) s) =
      (scalarEvaluationTransport T S c A U ≪≫
        (derivedSliceRestriction (ProEt.topology X) B' U).mapIso
          ((derivedComparison X B').mapIso αA)).symm ≪≫
      (S.localFunctor U).mapIso (derivedIsoEvaluation X B A D U hw s) ≪≫
      (scalarEvaluationTransport T S c D U ≪≫
        (derivedSliceRestriction (ProEt.topology X) B' U).mapIso
          ((derivedComparison X B').mapIso αD)) := by
  simp only [scalarConjugationReduction, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [derivedMorphism_isoEvaluation_natural, he]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_symm,
    Iso.symm_inv, Category.assoc]

include hS hc in
set_option backward.isDefEq.respectTransparency false in
theorem scalarConjugationReduction_square
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    {A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B'))}
    (dA : A ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj A')
    (dD : D ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj D')
    (αA : T.globalFunctor.obj A ≅ A') (αD : T.globalFunctor.obj D ≅ D')
    (hαA : aT.unit.app A ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map αA.hom = dA)
    (hαD : aT.unit.app D ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map αD.hom = dD)
    (U : X.ProEt) [IsAffine U.left]
    (hw : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (he : ∀ s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U),
      derivedIsoEvaluation X B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) U hw
          (((comparisonSetUpperStar X).map (T.isoSheafMap A D)).hom.app (op U) s) =
        (scalarEvaluationTransport T S c A U).symm ≪≫
          (S.localFunctor U).mapIso (derivedIsoEvaluation X B A D U hw s) ≪≫
            scalarEvaluationTransport T S c D U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)) :
    (derivedIsoEvaluation X B A D U hw s).hom ≫
        sliceComparisonNormalization X B B' φ dD U =
      sliceComparisonNormalization X B B' φ dA U ≫
        (Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ).map
          (derivedIsoEvaluation X B' A' D' U hw
            (((comparisonSetUpperStar X).map
              (scalarConjugationReduction X B B' T A D αA αD)).hom.app (op U) s)).hom := by
  rw [scalarConjugationReduction_evaluation X B B' T S c A D αA αD U hw he s,
    sliceComparisonNormalization_unit X B B' φ T S c aT aS aSL hS hc A A' dA αA hαA,
    sliceComparisonNormalization_unit X B B' φ T S c aT aS aSL hS hc D D' dD αD hαD]
  exact adjunct_conjugation_square (aSL U) _ _ _

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite
variable (X : Scheme.{u}) (B B' : Type (u + 1)) [CommRing B] [CommRing B']

theorem slice_normalized_iso_reduction [Finite B] [Finite B'] (φ : B →+* B')
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B')))
    (dA : A ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj A')
    (dD : D ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj D')
    (hA : StructuredArrow.IsUniversal (StructuredArrow.mk dA))
    (hD : StructuredArrow.IsUniversal (StructuredArrow.mk dD)) :
    ∃ r : derivedLocalIsoSheaf X.smallEtaleTopology B A D ⟶
      derivedLocalIsoSheaf X.smallEtaleTopology B' A' D',
      ∀ (U : X.ProEt) (ha : IsAffine U.left)
        (hw : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
        (s : ((comparisonSetUpperStar X).obj
          (derivedLocalIsoSheaf X.smallEtaleTopology B A D)).obj.obj (op U)),
        let := ha
        (derivedIsoEvaluation X B A D U hw s).hom ≫
            sliceComparisonNormalization X B B' φ dD U =
          sliceComparisonNormalization X B B' φ dA U ≫
            (Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) φ).map
              (derivedIsoEvaluation X B' A' D' U hw
                (((comparisonSetUpperStar X).map r).hom.app (op U) s)).hom := by
  classical
  obtain ⟨T, S, c, aT, aS, aTL, aSL, hTL, hSL, hc, he⟩ :=
    derivedMorphism_evaluation_scalarExtension X B B' φ
  let αA := StructuredArrow.universalIso (mkInitialOfLeftAdjoint _ aT A) hA (Iso.refl A)
  let αD := StructuredArrow.universalIso (mkInitialOfLeftAdjoint _ aT D) hD (Iso.refl D)
  have hαA : aT.unit.app A ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map αA.hom = dA := by
    simpa only [Iso.refl_hom, Category.id_comp] using
      StructuredArrow.universalIso_fac (mkInitialOfLeftAdjoint _ aT A) hA (Iso.refl A)
  have hαD : aT.unit.app D ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map αD.hom = dD := by
    simpa only [Iso.refl_hom, Category.id_comp] using
      StructuredArrow.universalIso_fac (mkInitialOfLeftAdjoint _ aT D) hD (Iso.refl D)
  refine ⟨scalarConjugationReduction X B B' T A D αA αD, ?_⟩
  intro U ha hw s
  let := ha
  exact scalarConjugationReduction_square X B B' φ T S c aT aS aSL hSL hc
    A D dA dD αA αD hαA hαD U hw (he A D U hw).2 s

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
set_option backward.isDefEq.respectTransparency false in
theorem source_slice_normalization (U : X.ProEt) (q : R →+* S)
    {A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {A' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (d : A ⟶ (normalizationRestrict X.smallEtaleTopology q).obj A') :
    (proetDerivedSliceRestrictionIso X R U).hom.app ((derivedComparison X R).obj A) ≫
      localProEtaleNormalization U.hom q d =
    (proetSliceEquivalence X R U).functor.mapDerivedCategory.map
      (sliceComparisonNormalization X R S q d U) ≫
      (proetDerivedSliceEquivalenceCoefficients X U q).hom.app
        ((derivedSliceRestriction (ProEt.topology X) S U).obj
          ((derivedComparison X S).obj A')) ≫
      (normalizationRestrict (ProEt.topology U.left) q).map
        ((proetDerivedSliceRestrictionIso X S U).hom.app ((derivedComparison X S).obj A')) := by
  have hp := proetDerivedSliceCoefficients_pasting X U q ((derivedComparison X S).obj A')
  have hn := (proetDerivedSliceRestrictionIso X R U).hom.naturality
    ((derivedComparison X R).map d ≫
      (comparisonRestrictScalarsIso X R q).hom.app A')
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [localProEtaleNormalization, localProEtaleComparisonCoefficients,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id, localProEtaleComparison, Functor.comp_map,
    Category.assoc, comparison_coefficient_derived_eq] at *
  rw [← CategoryTheory.Functor.map_comp_assoc]
  erw [← reassoc_of% hn]
  apply (cancel_mono ((normalizationRestrict (ProEt.topology U.left) q).map
    ((proetDerivedSliceRestrictionIso X S U).inv.app ((derivedComparison X S).obj A')))).mp
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [hp]
  simp only [sliceComparisonNormalization, CategoryTheory.Functor.map_comp,
    Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id, CategoryTheory.Functor.map_comp]
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) (R S : Type (u + 1)) [CommRing R] [CommRing S]
set_option backward.isDefEq.respectTransparency false in
/-- Universal arrows give reduction on local derived Isom sheaves, and canonical
source-site evaluation respects the specified normalization square.
Source: Stacks Tags 06YY, 098K, 09BV and 0F63
(blueprint: lem-weil-pbc-normalized-derived-isomorphism-transport).
Proof: use the scalar-extension adjunctions and their unit compatibility to conjugate
local isomorphisms by the unique isomorphisms supplied by the universal arrows.
Sheafify this natural conjugation. The existing weakly-contractible evaluation theorem
identifies its slice evaluation with scalar extension. Localization equivalences and
their canonical coefficient mates then transport this square to the source sites. -/
theorem source_normalized_iso_reduction [Finite R] [Finite S] (q : R →+* S)
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (A' D' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)))
    (dA : A ⟶ (normalizationRestrict X.smallEtaleTopology q).obj A')
    (dD : D ⟶ (normalizationRestrict X.smallEtaleTopology q).obj D')
    (hA : StructuredArrow.IsUniversal (StructuredArrow.mk dA))
    (hD : StructuredArrow.IsUniversal (StructuredArrow.mk dD)) :
    ∃ r : derivedLocalIsomorphismSheaf A D ⟶ derivedLocalIsomorphismSheaf A' D',
      ∀ (U : X.ProEt) (ha : IsAffine U.left)
        (hw : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
        (s : ((comparisonSetUpperStar X).obj
          (derivedLocalIsomorphismSheaf A D)).obj.obj (op U)),
      (sourceDerivedIsoEvaluation X R A D U ha hw s).hom ≫
          localProEtaleNormalization U.hom q dD =
        localProEtaleNormalization U.hom q dA ≫
          (normalizationRestrict (ProEt.topology U.left) q).map
            (sourceDerivedIsoEvaluation X S A' D' U ha hw
              (((comparisonSetUpperStar X).map r).hom.app (op U) s)).hom := by
  obtain ⟨r, hr⟩ := slice_normalized_iso_reduction X R S q A D A' D' dA dD hA hD
  let δ := etaleIsomorphismSheafIso X R A D
  let ε := etaleIsomorphismSheafIso X S A' D'
  refine ⟨δ.inv ≫ r ≫ ε.hom, ?_⟩
  intro U ha hw s
  let := ha
  let t := ((comparisonSetUpperStar X).map δ.inv).hom.app (op U) s
  have hs : ((comparisonSetUpperStar X).map ε.inv).hom.app (op U)
      (((comparisonSetUpperStar X).map (δ.inv ≫ r ≫ ε.hom)).hom.app (op U) s) =
      ((comparisonSetUpperStar X).map r).hom.app (op U) t := by
    have hm : (δ.inv ≫ r ≫ ε.hom) ≫ ε.inv = δ.inv ≫ r := by simp
    have hh := congrArg (fun f ↦ ((comparisonSetUpperStar X).map f).hom.app (op U) s) hm
    simpa only [CategoryTheory.Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, ConcreteCategory.comp_apply, t] using hh
  simp only [sourceDerivedIsoEvaluation]
  change _ = localProEtaleNormalization U.hom q dA ≫
    (normalizationRestrict (ProEt.topology U.left) q).map
      ((_ ≪≫ (proetSliceEquivalence X S U).functor.mapDerivedCategory.mapIso
        (derivedIsoEvaluation X S A' D' U hw
          (((comparisonSetUpperStar X).map ε.inv).hom.app (op U)
            (((comparisonSetUpperStar X).map (δ.inv ≫ r ≫ ε.hom)).hom.app (op U) s))) ≪≫
        _).hom)
  rw [hs]
  exact CategoryTheory.normalized_square_transport
    (proetSliceEquivalence X R U).functor.mapDerivedCategory
    (proetSliceEquivalence X S U).functor.mapDerivedCategory
    (Sheaf.derivedRestrictScalars ((ProEt.topology X).over U) q)
    (normalizationRestrict (ProEt.topology U.left) q)
    (proetDerivedSliceEquivalenceCoefficients X U q)
    ((proetDerivedSliceRestrictionIso X R U).app ((derivedComparison X R).obj A))
    ((proetDerivedSliceRestrictionIso X R U).app ((derivedComparison X R).obj D))
    ((proetDerivedSliceRestrictionIso X S U).app ((derivedComparison X S).obj A'))
    ((proetDerivedSliceRestrictionIso X S U).app ((derivedComparison X S).obj D'))
    (sliceComparisonNormalization X R S q dA U)
    (sliceComparisonNormalization X R S q dD U)
    (localProEtaleNormalization U.hom q dA) (localProEtaleNormalization U.hom q dD)
    (source_slice_normalization X U q dA) (source_slice_normalization X U q dD)
    (derivedIsoEvaluation X R A D U hw t)
    (derivedIsoEvaluation X S A' D' U hw
      (((comparisonSetUpperStar X).map r).hom.app (op U) t)) (hr U ha hw t)
end AlgebraicGeometry.Scheme
