/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ModuleCupGlobalTensorPullback
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Adjunction transpose polygon for the global cup

Source: Stacks, Tag 0FP3, specialized to the map to (pt, Γ(X,O_X)).
(blueprint: lem-sc-module-cup-adjunction-polygon)
This is the adjunction calculation for a chain pairing with K-injective
codomain. The argument passing to an arbitrary codomain is in the importing
compatibility module, by naturality and cancellation of a resolution.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

-- Share the tensor instances with the pullback comparison theorem.
attribute [local instance 2000] globalPullbackCommRing globalPullbackMonoidal
  globalPullbackSymmetric globalPullbackColimits globalPullbackPreadditive
  globalPullbackClosed globalPullbackFlatResolution

/-- The cochain pullback comparison, constructed from α and the localization isomorphisms.
Source: Stacks, Tags 0FP0 and 0FP1, comparison from derived to ordinary pullback.
(blueprint: def-sc-module-cup-cochain-pullback-comparison) -/
noncomputable def moduleCup_cochainPullbackComparison
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [P.Additive]
    (D : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ D ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ D ⟶
      P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))) D).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) α ≫
    (Functor.isoWhiskerLeft (P.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)))).hom

/-- Transport the tensor and counit squares from homotopy to cochain localization.
Source: Stacks, Tags 0FP0 and 0FP1; the quotient transport uses the canonical Qh/Q isomorphism.
(blueprint: lem-sc-module-cup-cochain-comparison-squares)
Proof: evaluate hTensor at the quotient images of A and B, and hCounit at the
quotient image of K. Conjugate their sides by quotientCompQhIso. Its naturality
moves localized chain maps across the isomorphism, and its tensor compatibility
identifies the lax comparisons of Qh and Q. The homotopy oplax comparison on
quotient objects is the quotient of the cochain comparison; the induced homotopy
counit on a quotient object is the quotient of the cochain counit. Substitute
these two equations. The definition of the cochain α comparison and of the
cochain β unit supplies exactly the remaining conjugating factors. Cancel
adjacent inverse/hom pairs and use associativity to obtain both displayed squares.
This is solely transport of the two assumed squares, independent of the naive
cup map and of adjunction transposition. -/
theorem moduleCup_cochain_comparison_squares
    (qLax :
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal)
    (hQ : qLax = DerivedCategory.laxMonoidalQ
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (β : (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
    (hβ : β =
      (Functor.isoWhiskerLeft
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))).inv ≫
        Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit ≫
        (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor).hom)
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace)
    (D : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ D ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (dAdj : D ⊣ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
    (δ : ∀ A B, D.obj (A ⊗ B) ≅ D.obj A ⊗ D.obj B)
    (hTensor : ∀ K M, moduleCup_globalTensorDiagram X P D α δ K M)
    (hCounit : ∀ K : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
      D.map ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K) ≫
        dAdj.counit.app (DerivedCategory.Qh.obj K) =
      α.app (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K)) :
    letI := qLax
    let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let Q₀ := DerivedCategory.Q
      (C := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let F := P.mapHomologicalComplex (ComplexShape.up ℤ)
    let a := moduleCup_cochainPullbackComparison X P D α
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    (∀ A B, D.map (Functor.LaxMonoidal.μ Q₀ A B) ≫ a.app (A ⊗ B) ≫
        Q.map (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
          (ComplexShape.up ℤ) P).app A).app B) =
      (δ (Q₀.obj A) (Q₀.obj B)).hom ≫ (a.app A ⊗ₘ a.app B) ≫
        Functor.LaxMonoidal.μ Q (F.obj A) (F.obj B)) ∧
    (∀ K, D.map (β.app K) ≫
        dAdj.counit.app (Q.obj K) =
      a.app (T.obj K) ≫ Q.map
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
