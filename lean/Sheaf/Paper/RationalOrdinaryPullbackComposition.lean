/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.RationalRealizationPullbackComparison
public import Sheaf.Paper.PbcActualRingedExchange

/-! # Ordinary rational coefficient composition and the normalized module and derived compositor.

Source: Bhatt--Scholze, Remark 6.8.15, p. 62; Stacks Tags 03CB, 0D6D, 07A4, 099N.
(blueprint: lem-per-rational-ordinary-pullback-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]


set_option maxHeartbeats 800000 in
-- Nested chart conversions arise in the explicit tensor-section normalization.
/-- Ordinary rational coefficient composition and the normalized module and derived compositor.
Source: Stacks Tags 03CB, 03EL, 0D6D and 07A4; BS Remark 6.8.15.

Proof: use the localization inverse-image unit and the coefficient projection equations
of localizedOrdinaryPullbackNormalization. The supplied rational_normalization fixes
each rational coefficient map on all inverse-image sections, so its localized
composite is the supplied composite coefficient. Sheafify balanced multiplication
e'' tensor (e' tensor m) to e'' d_h(e') tensor m, with inverse inserting one,
including the displayed fiber-product restriction. The module unit formulas and
balancing determine this map on local generators. On flat-term K-flat resolutions
this is a chain isomorphism and gives the ambient derived isomorphism. The
computation counits are the fixed counits of the same composite derived functors;
naturality of the derived comparison gives their displayed equation on every
complex. Its construction on resolving complexes determines the derived map;
no coefficient map is assumed invertible.
(blueprint: lem-per-rational-ordinary-pullback-composition). -/
theorem rationalOrdinaryPullbackComposition (g : Y ⟶ X) (h : Z ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (sZ : RationalModuleRealization l E Z)
    (ag : RationalRealizationPullbackComparison l E g sY sX)
    (ah : RationalRealizationPullbackComparison l E h sZ sY)
    (ac : RationalRealizationPullbackComparison l E (h ≫ g) sZ sX) :
    let unitSection {S T : Scheme.{u}} (g : S ⟶ T)
        (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
        (M : pbcModules T (rationalCoefficientSheaf l T E))
        (V : T.ProEt) (m : M.val.obj (op V)) :
        ((rationalPullModule l E g c).obj M).val.obj
          (op ((proEtaleBaseChange g).obj V)) :=
      pbcTensorSection c
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l T E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l T E)) (Iso.refl _) M V m)
    let scalarSection {S T : Scheme.{u}} (g : S ⟶ T)
        (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
        (V : T.ProEt) (e : (rationalCoefficientSheaf l T E).obj.obj (op V)) :
        (rationalCoefficientSheaf l S E).obj.obj (op ((proEtaleBaseChange g).obj V)) :=
      c.hom.app (op ((proEtaleBaseChange g).obj V))
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app
          (rationalCoefficientSheaf l T E)).hom.app (op V) e)
    let scalarMul (T : Scheme.{u})
        (M : pbcModules T (rationalCoefficientSheaf l T E)) (V : T.ProEtᵒᵖ)
        (e : (rationalCoefficientSheaf l T E).obj.obj V) (m : M.val.obj V) : M.val.obj V :=
      e • m
    (ac.rationalCoefficient =
    (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l X E) ≫
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map ag.rationalCoefficient ≫
      ah.rationalCoefficient) ∧
    ∃ (moduleComp : rationalPullModule l E g ag.rationalCoefficient ⋙
      rationalPullModule l E h ah.rationalCoefficient ≅
    rationalPullModule l E (h ≫ g) ac.rationalCoefficient),
    (∀ (M : pbcModules X (rationalCoefficientSheaf l X E)) (V : X.ProEt)
      (m : M.val.obj (op V))
      (e' : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange g).obj V)))
      (e'' : (rationalCoefficientSheaf l Z E).obj.obj
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))),
    (moduleComp.hom.app M).val.app
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
      (scalarMul Z
        ((rationalPullModule l E h ah.rationalCoefficient).obj
          ((rationalPullModule l E g ag.rationalCoefficient).obj M))
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V))) e''
        (unitSection h ah.rationalCoefficient
          ((rationalPullModule l E g ag.rationalCoefficient).obj M)
          ((proEtaleBaseChange g).obj V)
          (scalarMul Y
            ((rationalPullModule l E g ag.rationalCoefficient).obj M)
            (op ((proEtaleBaseChange g).obj V)) e'
            (unitSection g ag.rationalCoefficient M V m)))) =
      scalarMul Z
        ((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M)
        (op ((proEtaleBaseChange h).obj ((proEtaleBaseChange g).obj V)))
        (e'' * scalarSection h ah.rationalCoefficient
          ((proEtaleBaseChange g).obj V) e')
        (((rationalPullModule l E (h ≫ g) ac.rationalCoefficient).obj M).val.map
          ((MorphismProperty.Over.pullbackComp h g).inv.app V).op
            (unitSection (h ≫ g) ac.rationalCoefficient M V m))) ∧
    ∃ (ambientComp : rationalPullDerived l E g ag.rationalCoefficient ⋙
      rationalPullDerived l E h ah.rationalCoefficient ≅
    rationalPullDerived l E (h ≫ g) ac.rationalCoefficient),
    (∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    ambientComp.hom.app (DerivedCategory.Q.obj P) ≫
        rationalPullComplexCounit l E (h ≫ g) ac.rationalCoefficient P =
      (rationalPullDerived l E h ah.rationalCoefficient).map
          (rationalPullComplexCounit l E g ag.rationalCoefficient P) ≫
        rationalPullComplexCounit l E h ah.rationalCoefficient
          (((rationalPullModule l E g ag.rationalCoefficient).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex moduleComp (.up ℤ)).hom.app P)) := by sorry

end AlgebraicGeometry.Scheme
