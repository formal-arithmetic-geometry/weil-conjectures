/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # The cartesian equivalence for the overlap at a finite stage

Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: def-pc-perfect-overlap-stage-equivalence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The exact nested-open restriction agrees with derived pullback along its inclusion.
Source: Stacks Project, Tag 08DW, restriction of derived pullback.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
@[no_expose] noncomputable def overlapOpenInclusionPullbackIso (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U) :
    derivedPullback (X.homOfLE (leOfHom i)) ≅
      (schemeOpenOverlapRestriction X i).mapDerivedCategory := by
  classical
  let R := (schemeOpenRestriction X U).mapDerivedCategory
  let h := X.homOfLE (leOfHom i)
  let α : R ⋙ derivedPullback h ≅
      R ⋙ (schemeOpenOverlapRestriction X i).mapDerivedCategory :=
    Functor.isoWhiskerRight (singleComplexOpenPullbackIso X U).symm
        (derivedPullback h) ≪≫
      perfectHomComposition h U.ι ≪≫
        eqToIso (congrArg (fun k : W.toScheme ⟶ X ↦ derivedPullback.{u,w} k)
          (show h ≫ U.ι = W.ι from Scheme.homOfLE_ι X (leOfHom i))) ≪≫
          singleComplexOpenPullbackIso X W ≪≫
            (schemeDerivedOpenRestrictionCompIso X i).symm
  exact Classical.choose (Scheme.derived_open_restriction_iso_descent X U
    (derivedPullback h) (schemeOpenOverlapRestriction X i).mapDerivedCategory α)

/-- The chosen inclusion comparison is pinned to the exact nested-open
restriction after precomposition with global restriction. -/
theorem overlapOpenInclusionPullbackIso_whiskerLeft
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    let h := X.homOfLE (leOfHom i)
    Functor.isoWhiskerLeft R (overlapOpenInclusionPullbackIso X i) =
      Functor.isoWhiskerRight (singleComplexOpenPullbackIso X U).symm
          (derivedPullback h) ≪≫
        perfectHomComposition h U.ι ≪≫
          eqToIso (congrArg (fun k : W.toScheme ⟶ X ↦ derivedPullback.{u,w} k)
            (show h ≫ U.ι = W.ι from Scheme.homOfLE_ι X (leOfHom i))) ≪≫
            singleComplexOpenPullbackIso X W ≪≫
              (schemeDerivedOpenRestrictionCompIso X i).symm := by
  intro R h
  unfold overlapOpenInclusionPullbackIso
  exact Classical.choose_spec (Scheme.derived_open_restriction_iso_descent X U
    (derivedPullback h) (schemeOpenOverlapRestriction X i).mapDerivedCategory _)

/-- Component form of the pinned nested-open comparison. The exact restriction
isomorphism cancels the inverse factor in the defining descent equation. -/
theorem overlapOpenInclusionPullbackIso_hom_comp
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (M : schemeDerivedCategory X) :
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    let h := X.homOfLE (leOfHom i)
    ((overlapOpenInclusionPullbackIso X i).hom.app (R.obj M)) ≫
      (schemeDerivedOpenRestrictionCompIso X i).hom.app M =
      (derivedPullback h).map ((singleComplexOpenPullbackIso X U).inv.app M) ≫
        (perfectHomComposition h U.ι).hom.app M ≫
          (eqToIso (congrArg (fun k : W.toScheme ⟶ X ↦ derivedPullback.{u,w} k)
            (show h ≫ U.ι = W.ι from Scheme.homOfLE_ι X (leOfHom i)))).hom.app M ≫
            (singleComplexOpenPullbackIso X W).hom.app M := by
  intro R h
  have H := congrArg (fun e ↦ e.hom.app M)
    (overlapOpenInclusionPullbackIso_whiskerLeft X i)
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Category.assoc] at H
  rw [H]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [h]

/-- Inverse component equation, arranged to cancel the exact restriction
comparison before the open-inclusion pullback comparison. -/
theorem overlapOpenInclusionPullbackIso_inv_comp
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (M : schemeDerivedCategory X) :
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    let h := X.homOfLE (leOfHom i)
    (schemeDerivedOpenRestrictionCompIso X i).inv.app M ≫
        (overlapOpenInclusionPullbackIso X i).inv.app (R.obj M) =
      (singleComplexOpenPullbackIso X W).inv.app M ≫
        (eqToIso (congrArg (fun k : W.toScheme ⟶ X ↦ derivedPullback.{u,w} k)
          (show h ≫ U.ι = W.ι from Scheme.homOfLE_ι X (leOfHom i)))).inv.app M ≫
          (perfectHomComposition h U.ι).inv.app M ≫
            (derivedPullback h).map ((singleComplexOpenPullbackIso X U).hom.app M) := by
  intro R h
  have H := congrArg (fun e ↦ e.inv.app M)
    (overlapOpenInclusionPullbackIso_whiskerLeft X i)
  simp only [Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Iso.symm_inv] at H
  rw [H]
  simp only [Category.assoc]
  rw [← Category.assoc ((schemeDerivedOpenRestrictionCompIso X i).inv.app M)
    ((schemeDerivedOpenRestrictionCompIso X i).hom.app M),
    Iso.inv_hom_id_app, Category.id_comp]

/-- Derived pullback along the inverse of a scheme isomorphism, with its inverse
constructed from pullback along the isomorphism itself.
Source: Stacks Project, Tag 0D5S, composition and identity pullback.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def overlapSchemeIsoDerivedEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    schemeDerivedCategory X ≌ schemeDerivedCategory Y := by
  let identity : ∀ Z : Scheme.{u}, derivedPullback (𝟙 Z) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).2
  exact CategoryTheory.Equivalence.mk (derivedPullback e.inv) (derivedPullback e.hom)
    (perfectHomComposition e.hom e.inv ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) e.hom_inv_id) ≪≫ identity X).symm
    (perfectHomComposition e.inv e.hom ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) e.inv_hom_id) ≪≫ identity Y)

/-- The overlap inverse image is the base change of the original overlap.
The equivalence is constructed from the cartesian open-restriction square.
Source: Stacks Project, Tag 08DW, compatibility with open restriction.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def perfectOverlapStageEquivalence
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V : Y.Opens) :
    schemeDerivedCategory (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme ≌
      schemeDerivedCategory (pullback ((U ⊓ V).ι ≫ p) q) :=
  overlapSchemeIsoDerivedEquivalence
    ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback

/-- The stage equivalence carries exact restriction of a pulled-back object to
pullback of its restriction on the original overlap.
Source: Stacks Project, Tag 08DW, restriction and composition of pullback.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def perfectOverlapStageObjectIso
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L) :
    (derivedPullback (g ∣_ L) ⋙
      (schemeOpenOverlapRestriction X (homOfLE
        (show g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L from fun _ hx ↦ hWL hx))).mapDerivedCategory) ⋙
      (perfectOverlapStageEquivalence g p' p q h U V).functor ≅
    derivedPullback (Y.homOfLE hWL) ⋙
      derivedPullback (pullback.fst ((U ⊓ V).ι ≫ p) q) := by
  let hW' : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L := fun _ hx ↦ hWL hx
  let square := (isPullback_morphismRestrict g (U ⊓ V)).paste_vert h
  let e := square.isoPullback
  have restricted : X.homOfLE hW' ≫ (g ∣_ L) =
      (g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL := by
    apply (cancel_mono L.ι).1
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl
  have fac : e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
      pullback.fst ((U ⊓ V).ι ≫ p) q ≫ Y.homOfLE hWL := by
    calc
      e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
          e.inv ≫ ((g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL) := by rw [restricted]
      _ = (e.inv ≫ (g ∣_ (U ⊓ V))) ≫ Y.homOfLE hWL := by
            simp only [Category.assoc]
      _ = _ := by rw [square.isoPullback_inv_fst]
  change (derivedPullback (g ∣_ L) ⋙
    (schemeOpenOverlapRestriction X (homOfLE hW')).mapDerivedCategory) ⋙
    derivedPullback e.inv ≅ _
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _
        (overlapOpenInclusionPullbackIso X (homOfLE hW')).symm ≪≫
          perfectHomComposition (X.homOfLE hW') (g ∣_ L)) _ ≪≫
    perfectHomComposition e.inv (X.homOfLE hW' ≫ (g ∣_ L)) ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) fac) ≪≫
    (perfectHomComposition (pullback.fst ((U ⊓ V).ι ≫ p) q) (Y.homOfLE hWL)).symm

/-- Component equation for the pinned stage comparison, with the cartesian
factor associated in the order used by the pullback prism. -/
theorem perfectOverlapStageObjectIso_hom_app
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S)
    (q : T ⟶ S) (h : IsPullback g p' p q)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (A : schemeDerivedCategory L.toScheme) :
    let hW' : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L := fun _ hx ↦ hWL hx
    let e := ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback
    let fac : e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
        pullback.fst ((U ⊓ V).ι ≫ p) q ≫ Y.homOfLE hWL := by
      have restricted : X.homOfLE hW' ≫ (g ∣_ L) =
          (g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL := by
        apply (cancel_mono L.ι).1
        simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
        rw [← Category.assoc, Scheme.homOfLE_ι]
        rfl
      calc
        e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
            e.inv ≫ ((g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL) := by rw [restricted]
        _ = (e.inv ≫ (g ∣_ (U ⊓ V))) ≫ Y.homOfLE hWL := by
              simp only [Category.assoc]
        _ = _ := by rw [((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback_inv_fst]
    ((perfectOverlapStageObjectIso g p' p q h U V L hWL).app A).hom =
      ((Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (derivedPullback (g ∣_ L))
            (overlapOpenInclusionPullbackIso X (homOfLE hW')).symm ≪≫
            perfectHomComposition (X.homOfLE hW') (g ∣_ L))
          (derivedPullback e.inv) ≪≫
        perfectHomComposition e.inv (X.homOfLE hW' ≫ (g ∣_ L)) ≪≫
        eqToIso (congrArg (fun f ↦ derivedPullback f) fac) ≪≫
        (perfectHomComposition (pullback.fst ((U ⊓ V).ι ≫ p) q)
          (Y.homOfLE hWL)).symm).app A).hom := by
  intro hW' e fac
  rfl

/-- The apex equivalence first identifies the localized-open site with the actual
open subscheme, then applies the cartesian overlap equivalence.
Source: Stacks Project, Tags 08DW and 05RU.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def perfectOverlapApexEquivalence
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)))] :
    DerivedCategory (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V))) ≌
      schemeDerivedCategory (pullback ((U ⊓ V).ι ≫ p) q) := by
  letI := openComparisonOverModuleAbelian X.toRingedSpace (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)
  letI := openComparisonModuleAbelian (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme.toRingedSpace
  let e : SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)) ≌
      SheafOfModules.{u} (moduleRings (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv _
  letI : e.functor.IsEquivalence := e.isEquivalence_functor
  letI : e.inverse.IsEquivalence := e.isEquivalence_inverse
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  letI : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  exact e.mapDerivedCategory.trans
    (perfectOverlapStageEquivalence g p' p q h U V)

/-- The supplied local object isomorphism gives the object comparison at the apex.
Source: Stacks Project, Tag 08DW, restriction of the supplied pullback isomorphism.
(blueprint: def-pc-perfect-overlap-stage-equivalence). -/
noncomputable def perfectOverlapApexObjectIso
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S) (q : T ⟶ S)
    (h : IsPullback g p' p q) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (A : schemeDerivedCategory L.toScheme) (E : schemeDerivedCategory X)
    (φ : (derivedPullback (g ∣_ L)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ L)).mapDerivedCategory.obj E) :
    (perfectOverlapApexEquivalence g p' p q h U V).functor.obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory.obj E) ≅
    (derivedPullback (pullback.fst ((U ⊓ V).ι ≫ p) q)).obj
      ((derivedPullback (Y.homOfLE hWL)).obj A) := by
  let W' := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V
  let hW' : W' ≤ g ⁻¹ᵁ L := fun _ hx ↦ hWL hx
  letI := openComparisonOverModuleAbelian X.toRingedSpace W'
  letI := openComparisonModuleAbelian W'.toScheme.toRingedSpace
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W') ≌
      SheafOfModules.{u} (moduleRings W'.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv W'
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W'
  let SU := (schemeOpenOverlapRestriction X (homOfLE hW')).mapDerivedCategory
  let cart := perfectOverlapStageEquivalence g p' p q h U V
  change cart.functor.obj (e.functor.mapDerivedCategory.obj (R.mapDerivedCategory.obj E)) ≅ _
  exact cart.functor.mapIso
      ((Functor.mapDerivedCategoryCompIso R e.functor).symm.app E ≪≫
        (schemeDerivedOpenRestrictionCompIso X (homOfLE hW')).symm.app E ≪≫
        SU.mapIso φ.symm) ≪≫
    (perfectOverlapStageObjectIso g p' p q h U V L hWL).app A

end AlgebraicGeometry
