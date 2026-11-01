/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRingedDiagramRestrictionComparisons

/-!
# Derived adjunct comparison structures

Source: Stacks Project, Derived Categories, Tags 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-adjuncts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
namespace FlatRingedDiagramInput

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  {x : FlatRingedDiagramInput K H} {J : Type u} [SmallCategory J]
  [HasDerivedCategory.{w} (x.diagramsRU J)] [HasDerivedCategory.{w} (x.diagramsSU J)]
  [HasDerivedCategory.{w} (x.diagramsRV J)] [HasDerivedCategory.{w} (x.diagramsSV J)]
  {LR : derivedRV x J ⥤ derivedRU x J} {FR : derivedRU x J ⥤ derivedRV x J}
  {LS : derivedSV x J ⥤ derivedSU x J} {FS : derivedSU x J ⥤ derivedSV x J}

/-- The inverse-image localization normalization equation.
Source: Stacks 0FND (blueprint: def-weil-pbc-flat-ringed-diagram-adjuncts). -/
def inverseNormalized
    (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
    [HasDerivedCategory.{w} (x.diagramsRU J)] [HasDerivedCategory.{w} (x.diagramsSU J)]
    [HasDerivedCategory.{w} (x.diagramsRV J)] [HasDerivedCategory.{w} (x.diagramsSV J)]
    (LR : derivedRV x J ⥤ derivedRU x J) (FR : derivedRU x J ⥤ derivedRV x J)
    (LS : derivedSV x J ⥤ derivedSU x J) (FS : derivedSU x J ⥤ derivedSV x J)
    (maps : DerivedRestrictionComparisonMaps x J LR FR LS FS)
    (qLR : DerivedCategory.Q ⋙ LR ≅ inverseRComplex x J ⋙ DerivedCategory.Q)
    (qLS : DerivedCategory.Q ⋙ LS ≅ inverseSComplex x J ⋙ DerivedCategory.Q) : Prop :=
  ∀ P : cochainSV x J,
    maps.rU.map (qLS.hom.app P) ≫ maps.qU.hom.app ((inverseSComplex x J).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex maps.b0 (.up ℤ)).hom.app P) =
    maps.b.hom.app (DerivedCategory.Q.obj P) ≫ LR.map (maps.qV.hom.app P) ≫
      qLR.hom.app ((restrictVComplex x J).obj P)

/-- The direct-image right-derived-unit normalization equation.
Source: Stacks 0FND (blueprint: def-weil-pbc-flat-ringed-diagram-adjuncts). -/
def directNormalized
    (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
    [HasDerivedCategory.{w} (x.diagramsRU J)] [HasDerivedCategory.{w} (x.diagramsSU J)]
    [HasDerivedCategory.{w} (x.diagramsRV J)] [HasDerivedCategory.{w} (x.diagramsSV J)]
    (LR : derivedRV x J ⥤ derivedRU x J) (FR : derivedRU x J ⥤ derivedRV x J)
    (LS : derivedSV x J ⥤ derivedSU x J) (FS : derivedSU x J ⥤ derivedSV x J)
    (maps : DerivedRestrictionComparisonMaps x J LR FR LS FS)
    (ηS : directSComplex x J ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FS)
    (ηR : directRComplex x J ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FR) : Prop :=
  ∀ I : cochainSU x J,
    maps.rV.map (ηS.app I) ≫ maps.d.hom.app (DerivedCategory.Q.obj I) ≫
      FR.map (maps.qU.hom.app I) =
    maps.qV.hom.app ((directSComplex x J).obj I) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex maps.d0 (.up ℤ)).hom.app I) ≫
      ηR.app ((restrictUComplex x J).obj I)

end FlatRingedDiagramInput
end CategoryTheory
