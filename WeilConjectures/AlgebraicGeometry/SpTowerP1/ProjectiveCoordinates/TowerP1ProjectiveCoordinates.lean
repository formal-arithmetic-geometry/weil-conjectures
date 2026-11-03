/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1TensorCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleWords
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-projective-coordinates).

The coordinates retain the canonical associated-module-sheaf functor. Its tensor
comparison is fixed on scalar-unit pure tensors, on total-complex summands, and
on K-flat representatives. Thus the final level equations cannot be satisfied
by choosing unrelated isomorphisms of their endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]

variable {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- Positive coefficient exponent is invertible on the base.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev baseExponentUnit (hS : IsUnit (l : Γ(S, ⊤))) :
    IsUnit ((l ^ (n + 1) : ℕ) : Γ(S, ⊤)) := by
  simpa only [Nat.cast_pow] using hS.pow (n + 1)

/-- Positive coefficient exponent is invertible on the projective line.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev lineExponentUnit (hS : IsUnit (l : Γ(S, ⊤))) :
    IsUnit ((l ^ (n + 1) : ℕ) : Γ(ProjectiveLine S, ⊤)) :=
  finiteP1_unitOnPullback _ (ProjectiveLine S ↘ S) (baseExponentUnit l n hS)

/-- Positive coefficient exponent is invertible on the product.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev surfaceExponentUnit (hS : IsUnit (l : Γ(S, ⊤))) :
    IsUnit ((l ^ (n + 1) : ℕ) : Γ(diagonalSurface S, ⊤)) :=
  finiteP1_unitOnPullback _ (Etale.projectiveLineDiagonalProjection S false)
    (lineExponentUnit l n hS)

/-- Canonical coordinate data needed to read the ordinary etale words at one level.
Every nontrivial comparison is section- or representative-normalized above. The finite
splitting is specified by the unit and positive Chern map; its inverse fixes the trace.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
structure ProjectiveCoordinates (p : Presentation l E S hS) where
  geometric : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), GeometricCoordinates l E n f
  tensors : ∀ T : Scheme.{u}, TensorCoordinates l E n p.classes.base T
  coefficientsS : CoefficientCoordinates l E n S (baseExponentUnit l n hS)
  coefficientsP : CoefficientCoordinates l E n (ProjectiveLine S) (lineExponentUnit l n hS)
  coefficientsW : CoefficientCoordinates l E n (diagonalSurface S) (surfaceExponentUnit l n hS)
  transport : Etale.OrdinaryFiniteTwistTransport (levelRing l E n) (l ^ (n + 1))
    (levelAnnihilates l E n)
  splitting : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
    (levelAnnihilates l E n) transport S (baseExponentUnit l n hS)
  invertible : EtaleWords.InvertibleWords (levelRing l E n) (l ^ (n + 1))
    (levelAnnihilates l E n) S

variable {p : Presentation l E S hS}

/-- Direct-image word in the given projective presentation.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev ProjectiveCoordinates.push (c : ProjectiveCoordinates l E n p)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : LevelWord l E n X) :=
  pushWord l E n p.classes.base (p.operations.geometry f) (c.geometric f) K

/-- Inverse-image word in the given projective presentation.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev ProjectiveCoordinates.pull (c : ProjectiveCoordinates l E n p)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : LevelWord l E n Y) :=
  pullWord l E n p.classes.base (p.operations.geometry f) (c.geometric f) K

/-- Tensor word in the given projective presentation.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev ProjectiveCoordinates.tensor (c : ProjectiveCoordinates l E n p)
    {T : Scheme.{u}} (K L : LevelWord l E n T) :=
  tensorWord l E n p.classes.base (c.tensors T) K L

/-- The base constant word with constant-section normalization.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev ProjectiveCoordinates.unitS (c : ProjectiveCoordinates l E n p) :=
  unitWord l E n S c.coefficientsS

/-- The projective-line constant word with constant-section normalization.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev ProjectiveCoordinates.unitP (c : ProjectiveCoordinates l E n p) :=
  unitWord l E n (ProjectiveLine S) c.coefficientsP

/-- The shifted projective-line root word with its fixed lineEvaluation.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev ProjectiveCoordinates.lineP (c : ProjectiveCoordinates l E n p) :=
  lineWord l E n p.classes.chernP c.coefficientsP

/-- The shifted product root word with its fixed lineEvaluation.
Source: Levels (blueprint: def-sp-p1-projective-coordinates). -/
abbrev ProjectiveCoordinates.lineW (c : ProjectiveCoordinates l E n p) :=
  lineWord l E n p.classes.chernW c.coefficientsW

/-- The ordinary scalar diagonal identity for either projection.
Source: Construction (blueprint: def-sp-p1-projective-coordinates). -/
abbrev diagonalIdentity (S : Scheme.{u}) (a : Bool) :
    diagonalImmersion S ≫ Etale.projectiveLineDiagonalProjection S a = 𝟙 (ProjectiveLine S) := by
  cases a
  · exact pullback.diagonal_fst _
  · exact pullback.diagonal_snd _

/-- Composition source for either projection, using the specified tower adjunctions.
Source: Construction (blueprint: def-sp-p1-projective-coordinates). -/
def Presentation.sourceUnitAt (p : Presentation l E S hS) (a : Bool)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :
    M ⟶ (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
        ((SpTowerShriek.push l E p.classes.base
          (p.operations.geometry (diagonalImmersion S))).obj M) :=
  (SpTowerShriek.adjunction l E p.classes.base
    (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).unit.app M ≫
  (SpTowerShriek.push l E p.classes.base
    (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map
      ((SpTowerShriek.adjunction l E p.classes.base
        (p.operations.geometry (diagonalImmersion S))).unit.app _ ≫
        (SpTowerShriek.push l E p.classes.base
          (p.operations.geometry (diagonalImmersion S))).map
            ((p.diagonalPull l E (Etale.projectiveLineDiagonalProjection S a)
              (diagonalIdentity S a)).hom.app M))

/-- The other proper exchange is the same mate with the two projections exchanged.
Source: Construction, proper exchange (blueprint: def-sp-p1-projective-coordinates). -/
def Presentation.exchangeSwap (p : Presentation l E S hS)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj ((p.F l E).obj M) ⟶
      (SpTowerShriek.push l E p.classes.base (p.operations.geometry
        (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
          ((SpTowerShriek.pull l E p.classes.base (p.operations.geometry
            (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj M) :=
  (SpTowerShriek.adjunction l E p.classes.base (p.operations.geometry
    (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).unit.app _ ≫
    (SpTowerShriek.push l E p.classes.base (p.operations.geometry
      (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
        ((SpTowerShriek.square l E p.classes.base p.operations
          (pullback.snd _ _) (pullback.fst _ _) (ProjectiveLine S ↘ S)
            (ProjectiveLine S ↘ S) pullback.condition.symm).hom.app ((p.F l E).obj M) ≫
          (SpTowerShriek.pull l E p.classes.base
            (p.operations.geometry (pullback.snd _ _))).map
              ((SpTowerShriek.adjunction l E p.classes.base
                (p.operations.geometry (ProjectiveLine S ↘ S))).counit.app M))

end AlgebraicGeometry.ProEtale.SpTowerP1
