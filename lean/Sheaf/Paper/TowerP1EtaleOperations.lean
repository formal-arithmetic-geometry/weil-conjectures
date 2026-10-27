/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import Sheaf.AlgebraicGeometry.CartierReductionData
public import Sheaf.Paper.DiagonalTowerSystem
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise

/-! # Ordinary etale words for the projective-line tower comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Construction and Levels
(blueprint: def-sp-p1-etale-operations).

These are formulas in the ordinary etale derived categories. The diagonal is the
positive supported Cartier Kummer boundary; the trace is the second projection
of the inverse unit/Chern splitting. No adjunction unit is selected instead.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerP1.EtaleWords

variable (A : Type (u + 1)) [CommRing A]

/-- Exact etale inverse image, with its canonical left-derived presentation.
Source: Construction (blueprint: def-sp-p1-etale-operations). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := Etale.ordinaryFinitePullback A f

/-- Ordinary total right-derived etale direct image.
Source: Construction (blueprint: def-sp-p1-etale-operations). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) := Etale.ordinaryFinitePushforward A f

/-- The same unbounded etale derived tensor used by the finite projection theorem.
Source: Construction (blueprint: def-sp-p1-etale-operations). -/
abbrev tensor (T : Scheme.{u}) := Etale.ordinaryFiniteTensor A T

/-- The counit-transpose projection, with the direct-image factor first.
Source: Construction (blueprint: def-sp-p1-etale-operations). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :=
  ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app N).app K

/-- Pullback of a projection along the diagonal is identity, using the specified
ordinary compositor and identity isomorphism, localized canonically.
Source: Construction, composition source (blueprint: def-sp-p1-etale-operations). -/
def diagonalPull (S : Scheme.{u}) (a : Bool) :
    pull A (Etale.projectiveLineDiagonalProjection S a) ⋙ pull A (diagonalImmersion S) ≅
      𝟭 (Etale.DerivedCategoryModule A (ProjectiveLine S)) :=
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (diagonalImmersion S)
    (Etale.projectiveLineDiagonalProjection S a) (𝟙 (ProjectiveLine S))
      (by cases a
          · exact (pullback.diagonal_fst _).symm
          · exact (pullback.diagonal_snd _).symm)).symm ≪≫
    Functor.leftDerivedFunctorNatIso _
      (Etale.upperStarId (ModuleCat.{u + 1} A) (ProjectiveLine S)) ≪≫
    (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The finite composition source is the pasted ordinary adjunction unit.
Source: Construction, source identification
(blueprint: def-sp-p1-etale-operations). -/
def sourceUnit (S : Scheme.{u}) (a : Bool)
    (M : Etale.DerivedCategoryModule A (ProjectiveLine S)) :
    M ⟶ (push A (Etale.projectiveLineDiagonalProjection S a)).obj
      ((push A (diagonalImmersion S)).obj M) :=
  (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (Etale.projectiveLineDiagonalProjection S a)).unit.app M ≫
    (push A (Etale.projectiveLineDiagonalProjection S a)).map
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (diagonalImmersion S)).unit.app _ ≫
        (push A (diagonalImmersion S)).map ((diagonalPull A S a).hom.app M))

/-- The supported projection followed by the specified identity pullback and scalar unitor.
Source: Construction (blueprint: def-sp-p1-etale-operations). -/
def diagonalProjection (S : Scheme.{u}) (a : Bool)
    (M : Etale.DerivedCategoryModule A (ProjectiveLine S)) :
    ((tensor A (diagonalSurface S)).obj
      ((push A (diagonalImmersion S)).obj (Etale.ordinaryFiniteUnit A (ProjectiveLine S)))).obj
        ((pull A (Etale.projectiveLineDiagonalProjection S a)).obj M) ⟶
      (push A (diagonalImmersion S)).obj M :=
  projection A (diagonalImmersion S) _ _ ≫
    (push A (diagonalImmersion S)).map
      (((tensor A (ProjectiveLine S)).obj (Etale.ordinaryFiniteUnit A (ProjectiveLine S))).map
        ((diagonalPull A S a).hom.app M) ≫
        ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) (ProjectiveLine S)).hom.app
          (Etale.ordinaryFiniteUnit A (ProjectiveLine S))).app M ≫
        (Etale.derivedTensorSingleUnitIso M).hom)

/-- Proper exchange for the Cartesian q/q square, including its flipped version.
It is the unit/square/counit mate, with exact/left-derived identifications.
Source: Construction (blueprint: def-sp-p1-etale-operations). -/
def exchange (S : Scheme.{u}) (a : Bool)
    (M : Etale.DerivedCategoryModule A (ProjectiveLine S)) :
    (pull A (ProjectiveLine S ↘ S)).obj ((push A (ProjectiveLine S ↘ S)).obj M) ⟶
      (push A (Etale.projectiveLineDiagonalProjection S (!a))).obj
        ((pull A (Etale.projectiveLineDiagonalProjection S a)).obj M) :=
  (Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S)).hom.app _ ≫
    (Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (by cases a
          · exact (IsPullback.of_hasPullback (ProjectiveLine S ↘ S)
              (ProjectiveLine S ↘ S)).toCommSq
          · exact (IsPullback.of_hasPullback (ProjectiveLine S ↘ S)
              (ProjectiveLine S ↘ S)).flip.toCommSq)).app M ≫
    (push A (Etale.projectiveLineDiagonalProjection S (!a))).map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (Etale.projectiveLineDiagonalProjection S a)).inv.app M)

end AlgebraicGeometry.ProEtale.SpTowerP1.EtaleWords
