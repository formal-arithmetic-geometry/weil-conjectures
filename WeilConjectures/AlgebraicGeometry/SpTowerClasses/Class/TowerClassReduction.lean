/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems

/-! # Reduction for canonical tower classes
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The total derived extension adjunction, specified before specializing its categories. -/
structure DerivedExtension {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] where
  adjunction : F ⊣ G
  derived : DerivedCategory C ⥤ DerivedCategory D
  epsilon : DerivedCategory.Q ⋙ derived ⟶
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : derived.IsLeftDerivedFunctor epsilon
    (HomologicalComplex.quasiIso C (.up ℤ))
  derivedAdjunction : derived ⊣ G.mapDerivedCategory
  transpose : ∀ (P : CochainComplex C ℤ) (Q : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q),
    (derivedAdjunction.homEquiv _ _)
      (epsilon.app P ≫ DerivedCategory.Q.map f) ≫
        G.mapDerivedCategoryFactors.hom.app Q =
      DerivedCategory.Q.map (((adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P Q) f)

/-- Source normalization for a derived extension, expressed in arbitrary abelian categories. -/
def DerivedExtension.sourceNormalization
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (r : DerivedExtension F G) {X : C} {Y : D}
    (e : r.derived.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor D 0).obj Y) (q : X ⟶ G.obj Y) : Prop :=
  (r.derivedAdjunction.homEquiv _ _) e.hom ≫
    (G.mapDerivedCategorySingleFunctor 0).hom.app Y =
      (DerivedCategory.singleFunctor C 0).map q

/-- Target normalization for a derived extension, retaining the boundary sign and shift. -/
def DerivedExtension.targetNormalization
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (r : DerivedExtension F G) (s : ShortComplex C) (hs : s.ShortExact) {Y : D}
    (e : r.derived.obj (((DerivedCategory.singleFunctor C 0).obj s.X₃)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj Y)⟦(2 : ℤ)⟧)
    (y : G.obj Y ≅ s.X₁) : Prop :=
  (r.derivedAdjunction.homEquiv _ _) e.hom ≫
    (G.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor D 0).obj Y) ≫
    ((G.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(2 : ℤ)⟧' ≫
    ((DerivedCategory.singleFunctor C 0).map y.hom)⟦(2 : ℤ)⟧' =
      hs.singleδ⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory C) (1 : ℤ) 1).inv.app
          ((DerivedCategory.singleFunctor C 0).obj s.X₁)

/-- Realize an extension as its ordinary derived morphism. -/
def extensionArrow {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] [HasExt.{w₂} C]
    {X Y : C} {n : ℕ} (e : Ext.{w₂} X Y n) :
    (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧ :=
  e.hom

/-- Transport the source normalization through the specified derived adjunction. -/
def unitNormalization {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : DerivedCategory C ⥤ DerivedCategory D) (G : D ⥤ C)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G.mapDerivedCategory) {X : C} {Y : D}
    (e : F.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor D 0).obj Y) (q : X ⟶ G.obj Y) : Prop :=
  (a.homEquiv _ _) e.hom ≫ (G.mapDerivedCategorySingleFunctor 0).hom.app Y =
    (DerivedCategory.singleFunctor C 0).map q

/-- Ordinary coefficient extension and its representative-normalized total derivation. -/
structure Reduction (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) where
  forget : Forget T B
  ordinary : Ab T ⥤ Systems T B
  [additive : ordinary.Additive]
  model : DerivedExtension ordinary forget.F

attribute [instance] Reduction.additive

/-- The normalized derived extension functor. -/
abbrev Reduction.derived {T : Scheme.{u}}
    {B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
    (r : Reduction T B) := r.model.derived

/-- The normalized derived extension adjunction. -/
abbrev Reduction.derivedAdjunction {T : Scheme.{u}}
    {B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
    (r : Reduction T B) := r.model.derivedAdjunction

/-- Exact functors transport a single-to-shifted-single arrow using their canonical
single and shift comparisons. -/
def mapSingleArrow {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} (n : ℤ)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    (DerivedCategory.singleFunctor D 0).obj (F.obj X) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (F.obj Y))⟦n⟧ :=
  (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
    F.mapDerivedCategory.map f ≫
    (F.mapDerivedCategory.commShiftIso n).hom.app
      ((DerivedCategory.singleFunctor C 0).obj Y) ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧'

/-- Transport an Ext class to an ordinary derived arrow with specified endpoints. -/
def mapExtensionEndpoints {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] [HasExt.{w₃} C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {X' Y' : D} (e : Ext.{w₃} X Y 1)
    (a : X' ⟶ F.obj X) (b : F.obj Y ⟶ Y') :
    (DerivedCategory.singleFunctor D 0).obj X' ⟶
      ((DerivedCategory.singleFunctor D 0).obj Y')⟦(1 : ℤ)⟧ :=
  (DerivedCategory.singleFunctor D 0).map a ≫
    mapSingleArrow F (1 : ℤ) e.hom ≫
    ((DerivedCategory.singleFunctor D 0).map b)⟦(1 : ℤ)⟧'

/-- Exactness of the recorded change of site. -/
instance comparisonColimits (T : Scheme.{u}) :
    PreservesFiniteColimits (comparisonUpperStar AddCommGrpCat.{u + 1} T) :=
  inferInstance

/-- The constant-sheaf comparison induced by the recorded site morphism. -/
def integerComparison (T : Scheme.{u}) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
      ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≅
    (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (((((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (Scheme.Etale.isTerminalMkId T)).comp
      (comparisonAdjunction AddCommGrpCat.{u + 1} T)).ofNatIsoRight
    ((Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso
      AddCommGrpCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)
      (op (Scheme.Etale.mk (𝟙 T))))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.isTerminalMkId T))).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The etale units extension of the Picard class, before site comparison. -/
def lineBundleEtaleClass (T : Scheme.{u}) (L : T.Pic) :
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((constantSheaf (Scheme.ProEt.topology T)
        AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
        (Scheme.proEtaleUnitsSheaf T))⟦(1 : ℤ)⟧ :=
  mapExtensionEndpoints (comparisonUpperStar AddCommGrpCat.{u + 1} T)
    (Scheme.Pic.toCohomologicalPicardGroup T L)
    (integerComparison T).inv (cartierUnitsComparison T)

/-- The actual line-bundle class, pulled to full pro-etale units and then made constant
as a tower. -/
def lineBundleClass (T : Scheme.{u}) (L : T.Pic) :
    (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧ :=
  mapSingleArrow (constant T) (1 : ℤ) (lineBundleEtaleClass T L)

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
