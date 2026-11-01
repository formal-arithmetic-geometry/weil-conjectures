/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerivedLinear
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedMappingAction.DerivedMappingOrdinaryAction
import WeilConjectures.CategoryTheory.DerivedMappingDescent.DerivedMappingDescent
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Construction of the natural map for a single derived functor

Source: Stacks Project, Tags 070I and 070K, and the single-functor construction of
lem-sf-derived-functor-mapping-complex-action.
(blueprint: lem-sf-derived-mapping-single-step-construction)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe b v u w k

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace CategoryTheory.DerivedMappingAction

variable {B : Type b} [CommRing B]
  [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))]
  {A A' : Type u} [Category.{v} A] [Abelian A] [Linear B A]
  [HasDerivedCategory.{w} A] [Category.{v} A'] [Abelian A'] [Linear B A']
  [HasDerivedCategory.{w} A']

omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
/-- The universal unit as a natural transformation on ordinary complexes.
Source: Stacks 070K (blueprint: lem-sf-derived-mapping-single-step-construction). -/
def Step.complexUnitNat (e : Step (B := B) A A') :
    e.original.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ e.derived where
  app X := e.complexUnit X
  naturality _ _ f := e.complexUnit_naturality f

omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
/-- The unit on complexes satisfies its complete target-shift square.
Source: Stacks 070Y (blueprint: lem-sf-derived-mapping-single-step-construction).
Proof: evaluate the natural transformation's shift compatibility and expand the two
composite-functor shift comparisons. -/
theorem Step.complexUnit_shift (e : Step (B := B) A A')
    (h : e.HasCanonicalShift) (Y : CochainComplex A ℤ) (n : ℤ) :
    DerivedCategory.Q.map
        (((e.original.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app Y) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app
        ((e.original.mapHomologicalComplex (.up ℤ)).obj Y) ≫ (e.complexUnit Y)⟦n⟧' =
    e.complexUnit (Y⟦n⟧) ≫ e.derived.map ((DerivedCategory.Q.commShiftIso n).hom.app Y) ≫
      (e.derived.commShiftIso n).hom.app (DerivedCategory.Q.obj Y) := by
  have := e.complexUnitNat_commShift h
  simpa only [Functor.commShiftIso_comp_hom_app, Step.complexUnitNat,
    Category.assoc] using NatTrans.shift_app_comm e.complexUnitNat n Y

omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
/-- The unit identifies termwise application to a map into a shift with its derived image.
Source: Stacks 070I and 070Y
(blueprint: lem-sf-derived-mapping-single-step-construction).
Proof: postcompose the unit's shift square by the termwise image of the map and use
naturality of the unit. Preservation of composition by the derived functor finishes. -/
theorem Step.complexUnit_shift_map (e : Step (B := B) A A')
    (h : e.HasCanonicalShift) {X Y : CochainComplex A ℤ} (n : ℤ) (f : X ⟶ Y⟦n⟧) :
    DerivedCategory.Q.map ((e.original.mapHomologicalComplex (.up ℤ)).map f) ≫
      DerivedCategory.Q.map
        (((e.original.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app Y) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app
        ((e.original.mapHomologicalComplex (.up ℤ)).obj Y) ≫ (e.complexUnit Y)⟦n⟧' =
    e.complexUnit X ≫
      e.derived.map (DerivedCategory.Q.map f ≫
        (DerivedCategory.Q.commShiftIso n).hom.app Y) ≫
      (e.derived.commShiftIso n).hom.app (DerivedCategory.Q.obj Y) := by
  rw [e.complexUnit_shift h, ← Category.assoc, ← Category.assoc,
    e.complexUnit_naturality]
  simp only [Functor.map_comp, Category.assoc]

omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
/-- On K-injective representatives, conjugating the termwise shifted map gives RF(f).
Source: Stacks 070I and 070Y
(blueprint: lem-sf-derived-mapping-single-step-construction).
Proof: use the preceding unit equation and precompose by the inverse unit of the source.
The representative comparisons are the inverse units, so the source factors cancel. -/
theorem Step.representative_shift_map (e : Step (B := B) A A')
    (h : e.HasCanonicalShift) (I J : CochainComplex A ℤ)
    [I.IsKInjective] [J.IsKInjective] (n : ℤ) (f : I ⟶ J⟦n⟧) :
    (e.representativeIso I).hom ≫
      DerivedCategory.Q.map ((e.original.mapHomologicalComplex (.up ℤ)).map f) ≫
      DerivedCategory.Q.map
        (((e.original.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app J) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app
        ((e.original.mapHomologicalComplex (.up ℤ)).obj J) ≫
      (e.representativeIso J).inv⟦n⟧' =
    e.derived.map (DerivedCategory.Q.map f ≫
      (DerivedCategory.Q.commShiftIso n).hom.app J) ≫
      (e.derived.commShiftIso n).hom.app (DerivedCategory.Q.obj J) := by
  rw [e.representativeIso_inv]
  rw [e.complexUnit_shift_map h]
  rw [← e.representativeIso_inv I]
  simp only [Iso.hom_inv_id_assoc]

private def kinjProperty (A : Type u) [Category.{v} A] [Abelian A] :
    ObjectProperty (CochainComplex A ℤ) := fun I ↦ I.IsKInjective

private def kinjToDerived (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : (kinjProperty A).FullSubcategory ⥤ DerivedCategory A :=
  (kinjProperty A).ι ⋙ DerivedCategory.Q

private instance kinjToDerived_full : (kinjToDerived A).Full where
  map_surjective := by
    intro I J f
    have : J.obj.IsKInjective := J.property
    obtain ⟨s, hs⟩ := CochainComplex.IsKInjective.exists_Q_map_eq I.obj J.obj f
    exact ⟨ObjectProperty.homMk s, hs⟩

private instance kinjToDerived_essSurj [Abelian.HasKInjectiveResolutions A] :
    (kinjToDerived A).EssSurj where
  mem_essImage P := by
    obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (DerivedCategory.Q.objPreimage P)
    have := hs
    exact ⟨⟨I, hI⟩, ⟨(asIso (DerivedCategory.Q.map s)).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso P⟩⟩

private instance kinjPair_full :
    ((kinjToDerived A).op.prod (kinjToDerived A)).Full where
  map_surjective {X Y} f := by
    refine ⟨((kinjToDerived A).op.preimage f.1, (kinjToDerived A).preimage f.2), ?_⟩
    apply Prod.hom_ext
    · change (kinjToDerived A).op.map ((kinjToDerived A).op.preimage f.1) = f.1
      exact (kinjToDerived A).op.map_preimage f.1
    · exact (kinjToDerived A).map_preimage f.2

private instance kinjPair_essSurj [Abelian.HasKInjectiveResolutions A] :
    ((kinjToDerived A).op.prod (kinjToDerived A)).EssSurj where
  mem_essImage P := by
    refine ⟨((kinjToDerived A).op.objPreimage P.1, (kinjToDerived A).objPreimage P.2), ?_⟩
    exact ⟨Iso.prod ((kinjToDerived A).op.objObjPreimageIso P.1)
      ((kinjToDerived A).objObjPreimageIso P.2)⟩

private def kinjComparisonIso (S : HomModel (B := B) A) :
    ((kinjProperty A).ι.op.prod (kinjProperty A).ι) ⋙ S.ordinary ⋙ DerivedCategory.Q ≅
      ((kinjToDerived A).op.prod (kinjToDerived A)) ⋙ S.hom :=
  NatIso.ofComponents (fun P ↦ by
    have : P.2.obj.IsKInjective := P.2.property
    have := S.resolved P.1.unop.obj P.2.obj
    exact asIso (S.comparison.app (op P.1.unop.obj, P.2.obj))) (by
      intro P Q f
      exact S.comparison.naturality
        (X := (op P.1.unop.obj, P.2.obj)) (Y := (op Q.1.unop.obj, Q.2.obj))
        (f.1.unop.hom.op, f.2.hom))

/-- A linear cochain map gives a natural derived mapping arrow, normalized on every
K-injective pair, without assuming the functor preserves K-injectivity.

Source: Stacks Project, Tags 070I and 070K; Steps 2--4 of
lem-sf-derived-functor-mapping-complex-action.
(blueprint: lem-sf-derived-mapping-single-step-construction).

Proof: Restrict to K-injective complexes. The ordinary comparison is invertible there.
Apply the given cochain map, follow by the target ordinary comparison, and conjugate by
the inverse universal units computing RF on K-injectives. These are natural transformations,
so their composite is natural. The inclusion of K-injective complexes into the derived
category is full and essentially surjective, as is its opposite/product. Descend the
composite along this functor. The representative formula follows from the recovery law
for descent and cancellation of the source comparison. -/
theorem singleStepMap [Abelian.HasKInjectiveResolutions A]
    (S : HomModel (B := B) A) (T : HomModel (B := B) A') (e : Step (B := B) A A')
    (c : S.ordinary ⟶
      ((e.original.mapHomologicalComplex (.up ℤ)).op.prod
        (e.original.mapHomologicalComplex (.up ℤ))) ⋙ T.ordinary) :
    ∃ a : S.hom ⟶ (e.derived.op.prod e.derived) ⋙ T.hom,
      ∀ (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective],
      S.comparison.app (op I, J) ≫ a.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J) =
        DerivedCategory.Q.map (c.app (op I, J)) ≫
          T.comparison.app
            (op ((e.original.mapHomologicalComplex (.up ℤ)).obj I),
              (e.original.mapHomologicalComplex (.up ℤ)).obj J) ≫
          T.hom.map
            (X := (op (DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj I)),
              DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj J)))
            (Y := (op (e.derived.obj (DerivedCategory.Q.obj I)),
              e.derived.obj (DerivedCategory.Q.obj J)))
            ((e.representativeIso I).hom.op, (e.representativeIso J).inv) := by
  let P := (kinjToDerived A).op.prod (kinjToDerived A)
  let a := DerivedMappingDescent.descend P (restrictedMap S T e c)
  refine ⟨a, ?_⟩
  intro I J hI hJ
  have := S.resolved I J
  have ha := congrArg (fun η ↦ η.app
    (op (⟨I, hI⟩ : (kinjProperty A).FullSubcategory),
      (⟨J, hJ⟩ : (kinjProperty A).FullSubcategory)))
    (DerivedMappingDescent.whisker_descend P (restrictedMap S T e c))
  change a.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J) = _ at ha
  rw [ha]
  change S.comparison.app (op I, J) ≫
    (inv (S.comparison.app (op I, J)) ≫ DerivedCategory.Q.map (c.app (op I, J)) ≫
      T.comparison.app
        (op ((e.original.mapHomologicalComplex (.up ℤ)).obj I),
          (e.original.mapHomologicalComplex (.up ℤ)).obj J) ≫
      T.hom.map
        (X := (op (DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj I)),
          DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj J)))
        (Y := (op (e.derived.obj (DerivedCategory.Q.obj I)),
          e.derived.obj (DerivedCategory.Q.obj J)))
        ((e.representativeIso I).hom.op, (e.representativeIso J).inv)) = _
  simp only [IsIso.hom_inv_id_assoc]

/-- The normalized natural arrow is constructed by full, essentially surjective descent.
Source: Stacks 070I and 09L9
(blueprint: lem-sf-derived-mapping-single-step-construction).
Proof: apply the descent construction to the componentwise ordinary cochain action. -/
theorem Step.mappingArrow_exists [Abelian.HasKInjectiveResolutions A]
    (e : Step (B := B) A A') (S : HomModel (B := B) A) (T : HomModel (B := B) A') :
    Nonempty (e.MappingArrow S T) := by
  obtain ⟨a, ha⟩ := singleStepMap S T e (ordinaryMapNat S T e.original)
  exact ⟨⟨a, ha⟩⟩

end CategoryTheory.DerivedMappingAction
