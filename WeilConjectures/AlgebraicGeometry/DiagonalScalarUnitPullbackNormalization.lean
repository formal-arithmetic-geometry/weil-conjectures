/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalScalarPullbackComparison
import WeilConjectures.AlgebraicGeometry.OrdinarySemilinearPullbackSquare
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # The scalar/pullback square on coefficient units -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem scalar_mate_endpoint
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {T : A ⥤ B} {U : B ⥤ A} {S : C ⥤ D} {V : D ⥤ C}
    (a : T ⊣ U) (b : S ⊣ V) (F : A ⥤ C) (G : B ⥤ D)
    (e : G ⋙ V ≅ U ⋙ F)
    {M : A} {M' : B} {P : C} {P' : D}
    (c : T.obj M ⟶ M') (d : S.obj P ⟶ P')
    (p : F.obj M ⟶ P) (q : G.obj M' ⟶ P')
    (h : F.map (a.homEquiv _ _ c) ≫ e.inv.app M' ≫ V.map q =
      p ≫ b.homEquiv _ _ d) :
    (Adjunction.pushHomOfComapIso a b e).app M ≫ G.map c ≫ q = S.map p ≫ d := by
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hm := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ e.inv) M
  change F.map (a.unit.app M) ≫ e.inv.app (T.obj M) =
    b.unit.app (F.obj M) ≫
      V.map ((Adjunction.pushHomOfComapIso a b e).app M) at hm
  rw [← reassoc_of% hm]
  have hn := e.inv.naturality c
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← F.map_comp_assoc]
  have hp := b.unit.naturality p
  dsimp only [Functor.id_map, Functor.comp_map] at hp
  rw [← reassoc_of% hp]
  simpa only [Adjunction.homEquiv_unit] using h

variable {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
  (a : R ⟶ T) [IsMonHom a]


private theorem ordinary_regular_unit_square
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eS : Endpoint a (Mod.regular (condensedRingObj R S))
      (Mod.regular (condensedRingObj T S)) (coefficientMap a S))
    (eX : Endpoint a (Mod.regular (condensedRingObj R X))
      (Mod.regular (condensedRingObj T X)) (coefficientMap a X))
    (p₀ : UnitPullEndpoint R f) (p : UnitPullEndpoint T f) :
    (CondensedRing.upperStar R f).map eS.semilinear.hom ≫
        (CondensedRing.comapUpperStarIso a f).inv.app
          (Mod.regular (condensedRingObj T S)) ≫
      (Mod.comap (coefficientMap a X)).map p.iso.hom =
      p₀.iso.hom ≫ eX.semilinear.hom := by
  apply CondensedRing.ordinarySemilinearPullbackSquare a f _ _ _ _
    eS.semilinear.hom eX.semilinear.hom p₀.iso.hom p.iso.hom
  rw [p.normalization, p₀.normalization, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, eS.semilinear.underlying, eX.semilinear.underlying]
  exact map_coefficientMap_comp_condensedPullbackHom a f


attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor

private theorem exact_restriction_pull_single
    {X S : Scheme.{u}} (f : X ⟶ S) (M : Modules T S) :
    (CondensedRing.derivedComapUpperStarIso a f).inv.app
        ((DerivedCategory.singleFunctor (Modules T S) 0).obj M) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map
        (((CondensedRing.upperStar T f).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).hom.app
        ((CondensedRing.upperStar T f).obj M) =
    (CondensedRing.upperStar R f).mapDerivedCategory.map
        (((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((CondensedRing.upperStar R f).mapDerivedCategorySingleFunctor 0).hom.app
        ((Mod.comap (coefficientMap a S)).obj M) ≫
      (DerivedCategory.singleFunctor (Modules R X) 0).map
        ((CondensedRing.comapUpperStarIso a f).inv.app M) := by
  unfold CondensedRing.derivedComapUpperStarIso
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor
    (CondensedRing.upperStar T f) (Mod.comap (coefficientMap a X))
    (Mod.comap (coefficientMap a S) ⋙ CondensedRing.upperStar R f)
    (CondensedRing.comapUpperStarIso a f).symm M]
  erw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor
    (Mod.comap (coefficientMap a S)) (CondensedRing.upperStar R f) M]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

set_option maxHeartbeats 1600000 in
-- Explicit comparison expressions require additional definitional-equality checking.
private theorem restriction_pull_single
    {X S : Scheme.{u}} (f : X ⟶ S) (M : Modules T S) :
    (derivedUpper R f).map
        (((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).inv.app M) ≫
      (scalarRestrictionPullbackIso a f).inv.app
        ((DerivedCategory.singleFunctor (Modules T S) 0).obj M) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map (singlePullback T f M).hom ≫
      ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).hom.app
        ((CondensedRing.upperStar T f).obj M) =
    (singlePullback R f ((Mod.comap (coefficientMap a S)).obj M)).hom ≫
      (DerivedCategory.singleFunctor (Modules R X) 0).map
        ((CondensedRing.comapUpperStarIso a f).inv.app M) := by
  unfold derivedUpper scalarRestrictionPullbackIso singlePullback
    Functor.singleFunctorCompLeftDerivedFunctorIso
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  have hc :
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory T f).inv.app
          ((DerivedCategory.singleFunctor (Modules T S) 0).obj M) ≫
        (CondensedRing.upperStar T f).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.singleFunctor (Modules T S) 0).obj M) = 𝟙 _ := by
    exact (CondensedRing.upperStar T f).leftDerivedFunctorIsoMapDerivedCategory.inv_hom_id_app _
  erw [← (Mod.comap (coefficientMap a X)).mapDerivedCategory.map_comp_assoc, hc,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [exact_restriction_pull_single a f M]
  have hn := (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom.naturality
    (((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).inv.app M)
  erw [reassoc_of% hn]
  erw [← (CondensedRing.upperStar R f).mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option maxHeartbeats 1600000 in
-- Cancellation compares the large exact-derived single-functor expressions.
private theorem derived_scalar_unit_pullback_transpose
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eS : Endpoint a (Mod.regular (condensedRingObj R S))
      (Mod.regular (condensedRingObj T S)) (coefficientMap a S))
    (eX : Endpoint a (Mod.regular (condensedRingObj R X))
      (Mod.regular (condensedRingObj T X)) (coefficientMap a X))
    (p₀ : UnitPullEndpoint R f) (p : UnitPullEndpoint T f)
    (hOrd :
      (CondensedRing.upperStar R f).map eS.semilinear.hom ≫
          (CondensedRing.comapUpperStarIso a f).inv.app
            (Mod.regular (condensedRingObj T S)) ≫
        (Mod.comap (coefficientMap a X)).map p.iso.hom =
        p₀.iso.hom ≫ eX.semilinear.hom) :
    (derivedUpper R f).map
        ((DerivedCategory.singleFunctor (Modules R S) 0).map eS.semilinear.hom ≫
          ((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).inv.app
            (Mod.regular (condensedRingObj T S))) ≫
      (scalarRestrictionPullbackIso a f).inv.app
        ((DerivedCategory.singleFunctor (Modules T S) 0).obj
          (Mod.regular (condensedRingObj T S))) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map p.derived =
      p₀.derived ≫
        (DerivedCategory.singleFunctor (Modules R X) 0).map eX.semilinear.hom ≫
          ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app
            (Mod.regular (condensedRingObj T X)) := by
  unfold PullEndpoint.derived derivedUpper
  apply (cancel_mono
    (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).hom.app
      (Mod.regular (condensedRingObj T X)))).mp
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  have hn := ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).hom.naturality
    p.iso.hom
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  have hsingle := restriction_pull_single a f (Mod.regular (condensedRingObj T S))
  erw [reassoc_of% hsingle]
  have hm := (Functor.singleFunctorCompLeftDerivedFunctorIso
    (CondensedRing.upperStar R f)).hom.naturality eS.semilinear.hom
  dsimp only [Functor.comp_map] at hm
  erw [reassoc_of% hm]
  simpa only [derivedUpper, singlePullback, Iso.app_hom, Functor.comp_obj, Functor.map_comp,
    Category.assoc, Category.comp_id] using
    congrArg (fun k ↦ (singlePullback R f (Mod.regular (condensedRingObj R S))).hom ≫
      (DerivedCategory.singleFunctor (Modules R X) 0).map k) hOrd


set_option maxHeartbeats 800000 in
-- Matching the scalar-adjunction normalizations unfolds large functor expressions.
/-- The scalar mate preserves normalized regular-module pullback endpoints.

Source: latest blueprint, diagonal coefficient changes, proof paragraph (3),
the coefficient-unit boundary of the trace pasting argument.
(blueprint: lem-diagonal-scalar-unit-pullback-normalization).

Proof: transpose through extension/restriction at X. The unit equation for
mates replaces the scalar comparison by restriction commuting with pullback.
The two Endpoint normalizations replace their transposes by the singles of the
coefficient maps. Exact pullback and restriction commute with the single
functor. The ordinary PullEndpoint normalizations reduce the resulting module
square to naturality of the coefficient map with condensedPullbackHom. This
naturality is the defining coefficient square, so faithfulness of the module
forgetful functor proves it. Transpose back by the derived scalar adjunction.
No coefficient extension is assumed exact. -/
theorem scalar_unit_pullback_normalization
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eS : Endpoint a (Mod.regular (condensedRingObj R S))
      (Mod.regular (condensedRingObj T S)) (coefficientMap a S))
    (eX : Endpoint a (Mod.regular (condensedRingObj R X))
      (Mod.regular (condensedRingObj T X)) (coefficientMap a X))
    (p₀ : UnitPullEndpoint R f) (p : UnitPullEndpoint T f) :
    (scalarPullbackComparison a f).app (unit R S) ≫
        (derivedUpper T f).map eS.iso.hom ≫ p.derived =
      (derivedScalars a X).map p₀.derived ≫ eX.iso.hom := by
  let adS := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S)
  let adX := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  apply scalar_mate_endpoint adS adX (derivedUpper R f) (derivedUpper T f)
    (scalarRestrictionPullbackIso a f) eS.iso.hom eX.iso.hom p₀.derived p.derived
  dsimp only [adS, adX]
  rw [eS.normalization, eX.normalization]
  apply derived_scalar_unit_pullback_transpose a f eS eX p₀ p
  exact ordinary_regular_unit_square a f eS eX p₀ p

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
