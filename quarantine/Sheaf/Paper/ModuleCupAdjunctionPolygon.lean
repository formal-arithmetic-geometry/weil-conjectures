/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ModuleCupGlobalTensorPullback
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Paper.ModuleCupAdjunctionCalculation
import Sheaf.Paper.ModuleCupCochainCounitTensor
import Sheaf.Paper.ModuleCupCochainComparisonSquares

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

local instance polygonCommRing : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

local instance polygonMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  moduleTensor X
local instance polygonSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf

local instance polygonColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _

local instance polygonPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
local instance polygonClosed : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance polygonFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X

-- Share the tensor instances with the pullback comparison theorem.
attribute [local instance 2000] globalPullbackCommRing globalPullbackMonoidal
  globalPullbackSymmetric globalPullbackColimits globalPullbackPreadditive
  globalPullbackClosed globalPullbackFlatResolution

set_option maxHeartbeats 1000000 in
-- Elaborating the concrete localization and tensor instances requires additional heartbeats.
/-- Compatibility of the explicit adjunction transpose of the tensor counits.
Source: Stacks, Tags 0FP3 (Lemma 20.31.3), 0FP1 and 0FP0.
(blueprint: lem-sc-module-cup-adjunction-polygon)
Proof: use hQ to identify the supplied lax localization structure with the
canonical one, and hβ to identify the supplied comparison with its canonical
transported unit. Use hμ to substitute the specified adjunction transpose.
Then transpose both sides through dAdj. Naturality of δ moves the
tensor of the comparison units through the derived tensor constraint.
Naturality of its Hom equivalence
moves the two comparison units and the final localized pairing to the source
side. The assumed counit square replaces each derived counit after the unit by
α followed by ordinary evaluation. Apply the assumed tensor diagram at the
two homotopy complexes of sections; its two paths identify the tensor of these
comparisons with the comparison on the total tensor. Naturality of α moves the
ordinary tensor map to the right. The ordinary tensor/counit equation identifies
its degreewise components with evaluation on tensor sections. Passing to total
complexes, the coproduct inclusions defining moduleCup_naiveMap identify the
resulting chain map with the tensor of sections followed by φ. The comparison
β is the homotopy right-derived unit transported through quotientCompQhIso;
its naturality transports this same equation to cochain localization. Injectivity
of the inverse Hom equivalence gives the displayed equality. This argument uses
the concrete maps and the counit square, not merely naturality of an arbitrary
pairing. It applies in all degrees; neither K nor L is assumed flat or bounded. -/
theorem moduleCup_adjunction_polygon
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
    (hNat : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      D.map (f ⊗ₘ g) ≫ (δ A' B').hom =
        (δ A B).hom ≫ (D.map f ⊗ₘ D.map g))
    (hTensor : ∀ K M, moduleCup_globalTensorDiagram X P D α δ K M)
    (hCounit : ∀ K : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
      D.map ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K) ≫
        dAdj.counit.app (DerivedCategory.Qh.obj K) =
      α.app (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K))
    (hOrdinary : ∀ M N : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      Functor.LaxMonoidal.μ P
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N) ≫
        P.map (moduleCup_sectionTensorMap X M N) ≫ adj.counit.app (M ⊗ N) =
          adj.counit.app M ⊗ₘ adj.counit.app N)
    (μ : ∀ A B : DerivedCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj (A ⊗ B))
    (hμ : μ = fun A B ↦
      dAdj.homEquiv
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B)
        (A ⊗ B)
        ((δ ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A)
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B)).hom ≫
          (dAdj.counit.app A ⊗ₘ dAdj.counit.app B))) :
    letI := qLax
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let T := S.mapHomologicalComplex (ComplexShape.up ℤ)
    let R := S.rightDerivedFunctor
    ∀ (K L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      [I.IsKInjective] (φ : K ⊗ L ⟶ I),
      (β.app K ⊗ₘ β.app L) ≫ μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        R.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫ DerivedCategory.Q.map φ) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (T.obj K) (T.obj L) ≫
        DerivedCategory.Q.map (moduleCup_naiveMap X K L ≫ T.map φ) ≫ β.app I := by
  dsimp only
  rw [hμ]
  dsimp only
  intro K L I inst φ
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let T := S.mapHomologicalComplex (ComplexShape.up ℤ)
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let Q₀ := DerivedCategory.Q
    (C := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
  let F := P.mapHomologicalComplex (ComplexShape.up ℤ)
  let a := moduleCup_cochainPullbackComparison X P D α
  let : Q.LaxMonoidal := qLax
  obtain ⟨ht, hc⟩ := moduleCup_cochain_comparison_squares X qLax hQ β hβ P adj D α dAdj δ
    hTensor hCounit
  exact moduleCup_polygon_calculation Q Q₀ T F D S.rightDerivedFunctor
    (adj.mapHomologicalComplex (ComplexShape.up ℤ)) dAdj a β δ hNat
    (fun A B ↦ ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
      (ComplexShape.up ℤ) P).app A).app B) ht hc K L I
    (moduleCup_naiveMap X K L) (moduleCup_cochain_counit_tensor X P adj hOrdinary K L) φ

end
end AlgebraicGeometry.Scheme.Modules
