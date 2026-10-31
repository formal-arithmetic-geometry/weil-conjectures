/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteIntrinsicRealizationComparisons
import all WeilConjectures.AlgebraicGeometry.FiniteDirectCounitFixedRealizationTransport

/-! # Normalized finite adjunction in inverse realization coordinates

Source: Stacks 07A5 and 07A6, localization of the section-normalized adjunction.
(blueprint: lem-sf-finite-intrinsic-adjunction-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open FiniteIntrinsicRealization

private theorem unit_compat_of_counit
    {X Y x y : Type*} [Category X] [Category Y] [Category x] [Category y]
    {P : Y ⥤ X} {R : X ⥤ Y} {p : y ⥤ x} {r : x ⥤ y}
    (a : P ⊣ R) (b : p ⊣ r) (F : X ⥤ x) (G : Y ⥤ y)
    (ep : P ⋙ F ≅ G ⋙ p) (er : R ⋙ G ≅ F ⋙ r)
    (hc : ∀ M, ep.hom.app (R.obj M) ≫ p.map (er.hom.app M) ≫
      b.counit.app (F.obj M) = F.map (a.counit.app M)) (N : Y) :
    G.map (a.unit.app N) ≫ er.hom.app (P.obj N) ≫ r.map (ep.hom.app N) =
      b.unit.app (G.obj N) := by
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [b.counit_naturality]
  have hh : p.map (er.hom.app (P.obj N)) ≫ b.counit.app (F.obj (P.obj N)) =
      ep.inv.app (R.obj (P.obj N)) ≫ F.map (a.counit.app (P.obj N)) := by
    rw [← hc]
    simp only [Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc (p.map (er.hom.app (P.obj N))), hh]
  have hn := ep.inv.naturality (a.unit.app N)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc, ← F.map_comp, a.left_triangle_components]
  erw [F.map_id, Category.id_comp, Iso.inv_hom_id_app]
  exact (b.left_triangle_components (G.obj N)).symm

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence CategoryTheory.constantSheaf
  HasDerivedCategory.standard AlgebraicGeometry.Scheme.residueField
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence Functor.mapHomologicalComplex
  CompactSupportFiniteProjection.realization sixFunctorFiniteRealization

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The two normalized realization squares preserve the actual unit and counit.
Source: Stacks 07A5 and 07A6; section-normalized coefficient comparison.
(blueprint: lem-sf-finite-intrinsic-adjunction-realization).

Proof: on sheaves the actual adjunction is conjugation of the fixed adjunction
through the coefficient equivalences and the section-normalized direct-image
comparison. Its unit and counit therefore satisfy these equations before
localization, by the equivalence triangle identities. Apply exact termwise
localization to the pullback square. On K-injective complexes the normalized
right-derived direct-image comparison is the ordinary section comparison followed
by the two localization factors. The derived adjunction formulas for the unit and
counit identify the same maps on these representatives. Naturality transports the
equations along a K-injective resolution, and cancellation of the resolution
isomorphisms proves the equations on arbitrary unbounded derived objects. Finally
use the canonical comparison between exact pullback and left-derived pullback.
The construction works for zero objects, empty schemes and m = 0. -/
theorem finiteIntrinsicAdjunctionRealization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let RX := CompactSupportFiniteProjection.realization (C := C) (E := E)
      (n := m + 1) (hn := Nat.le_add_left 1 m) X
    let RY := CompactSupportFiniteProjection.realization (C := C) (E := E)
      (n := m + 1) (hn := Nat.le_add_left 1 m) Y
    let P := finiteDerivedPullback C.l E m f.hom.left
    let R := proEtaleConstantDerivedDirectImage f.hom.left A
    let Pf := (upperStar B f.hom.left).leftDerivedFunctor
    let Rf := (lowerStar B f.hom.left).rightDerivedFunctor
    let a := IntegralSystemRealization.finiteAdj C.l E f.hom.left m
    let b := derivedUpperStarLowerStarAdjunction B f.hom.left
    let ep := inversePullback (C := C) (E := E) m f
    let er := inverseDirectImage (C := C) (E := E) m f
    (∀ N, RY.inverse.map (a.unit.app N) ≫ er.hom.app (P.obj N) ≫
      Rf.map (ep.hom.app N) = b.unit.app (RY.inverse.obj N)) ∧
    (∀ M, ep.hom.app (R.obj M) ≫ Pf.map (er.hom.app M) ≫
      b.counit.app (RX.inverse.obj M) = RX.inverse.map (a.counit.app M))  := by
  dsimp only
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let RX := CompactSupportFiniteProjection.realization (C := C) (E := E)
    (n := m + 1) (hn := Nat.le_add_left 1 m) X
  let RY := CompactSupportFiniteProjection.realization (C := C) (E := E)
    (n := m + 1) (hn := Nat.le_add_left 1 m) Y
  let P := finiteDerivedPullback C.l E m f.hom.left
  let R := proEtaleConstantDerivedDirectImage f.hom.left A
  let Pf := (upperStar B f.hom.left).leftDerivedFunctor
  let Rf := (lowerStar B f.hom.left).rightDerivedFunctor
  let a := IntegralSystemRealization.finiteAdj C.l E f.hom.left m
  let b := derivedUpperStarLowerStarAdjunction B f.hom.left
  let ep := inversePullback (C := C) (E := E) m f
  let er := inverseDirectImage (C := C) (E := E) m f
  let L := (upperStar B f.hom.left).mapDerivedCategory
  let e := leftDerivedUpperStarIsoMapDerivedCategory B f.hom.left
  let o := Functor.mapDerivedCategoryCompIso
    (sfIntrinsicModuleEquivalence Y.obj.left A).inverse
    ((upperStar B f.hom.left) ⋙ (sfIntrinsicModuleEquivalence X.obj.left A).functor) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
  have hep (N) : ep.hom.app N = RX.inverse.map (o.hom.app N) ≫
      RX.unitIso.inv.app (L.obj (RY.inverse.obj N)) ≫ e.inv.app (RY.inverse.obj N) := by
    simp only [ep, inversePullback, pullback, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp]
    simp only [o, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    erw [RX.unitIso.inv.naturality]
    rfl
  have hc : ∀ M, ep.hom.app (R.obj M) ≫ Pf.map (er.hom.app M) ≫
      b.counit.app (RX.inverse.obj M) = RX.inverse.map (a.counit.app M) := by
    intro M
    have ht := intrinsicDerivedCounit_coordinates A f.hom.left M
    have ha (K) := congrArg (fun z ↦ z.counit.app K)
      (exactProEtaleAdjunction_eq A f.hom.left)
    have hh := coordinate_counit_comp
      (sfIntrinsicModuleEquivalence Y.obj.left A).mapDerivedCategory
      (sfIntrinsicModuleEquivalence X.obj.left A).mapDerivedCategory
      L Pf Rf P R
      (upperStarLowerStarAdjunction B f.hom.left
        ).mapDerivedCategoryRightDerivedAdjunction b a e o
      (sfIntrinsicDerivedDirectImageComparison f.hom.left A) ha M (R.obj M)
      (P.obj (R.obj M)) (𝟙 _) (𝟙 _) ht
    simpa only [hep, er, inverseDirectImage, inverseComparison, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
      Functor.map_id, P.map_id, Functor.comp_map, Functor.comp_obj,
      Category.id_comp, Category.comp_id, Category.assoc,
      CompactSupportFiniteProjection.realization, sixFunctorFiniteRealization,
      sfIntrinsicDerivedEquivalence, RX, RY, A, Equivalence.unitInv, Equivalence.counitInv]
      using hh
  exact ⟨unit_compat_of_counit a b RX.inverse RY.inverse ep er hc, hc⟩

end WeilConjectures.IntegralProjectionReduction
