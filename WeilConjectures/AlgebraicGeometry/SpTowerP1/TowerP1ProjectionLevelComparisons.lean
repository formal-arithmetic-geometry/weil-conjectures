/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.ProjectiveCoordinates.TowerP1ProjectiveCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1TensorCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleWords
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-projection-level-comparisons).

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

variable {p : Presentation l E S hS}

/-- Actual projection square on a pair of words. Both endpoints are recursively
transported by the specified evaluation, witness, monoidal and site-mate comparisons.
Source: Levels (blueprint: def-sp-p1-projection-level-comparisons). -/
def projectionWord (c : ProjectiveCoordinates l E n p)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : LevelWord l E n X) (K : LevelWord l E n Y) : Prop :=
  WordComparison l E n (c.tensor l E n (c.push l E n f N) K)
    (c.push l E n f (c.tensor l E n N (c.pull l E n f K)))
    (SpTowerP1.projection l E (p.operations.geometry f) N.tower K.tower)
    (EtaleWords.projection (levelRing l E n) f N.etale K.etale)

/-- Level comparison of each of the specified projection maps for every retained origin.
Source: Levels (blueprint: def-sp-p1-projection-level-comparisons). -/
structure ProjectionLevelComparisons (c : ProjectiveCoordinates l E n p) : Prop where
  q : ∀ (K : C l E p.classes.base S)
    (o : SpTowerShriek.Origin l E p.classes.base S n K.obj),
    projectionWord l E n c (ProjectiveLine S ↘ S) (c.lineP l E n)
      (originWord l E n p.classes.base o)
  projections : ∀ (a : Bool) (M : C l E p.classes.base (ProjectiveLine S))
    (o : SpTowerShriek.Origin l E p.classes.base (ProjectiveLine S) n M.obj),
    projectionWord l E n c (Etale.projectiveLineDiagonalProjection S a) (c.lineW l E n)
      (originWord l E n p.classes.base o)
  diagonal : ∀ (a : Bool) (M : C l E p.classes.base (ProjectiveLine S))
    (o : SpTowerShriek.Origin l E p.classes.base (ProjectiveLine S) n M.obj),
    projectionWord l E n c (diagonalImmersion S) (c.unitP l E n)
      (c.pull l E n (Etale.projectiveLineDiagonalProjection S a)
        (originWord l E n p.classes.base o))

/-- Both exchange mates, with exactly the two specified projection orders.
Source: Construction (blueprint: def-sp-p1-projection-level-comparisons). -/
def Presentation.exchangeAt (p : Presentation l E S hS) (a : Bool)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj ((p.F l E).obj M) ⟶
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S (!a)))).obj
        ((SpTowerShriek.pull l E p.classes.base
          (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj M) :=
  match a with
  | false => p.exchange l E M
  | true => p.exchangeSwap l E M

/-- Exchange and composition squares with nu-star of the actual ordinary etale words.
The universal quantifier retains the caller's origin, rather than choosing a new lift.
Source: Levels (blueprint: def-sp-p1-projection-level-comparisons). -/
structure ExchangeLevelComparisons (c : ProjectiveCoordinates l E n p) : Prop where
  exchange : ∀ (a : Bool) (M : C l E p.classes.base (ProjectiveLine S))
    (o : SpTowerShriek.Origin l E p.classes.base (ProjectiveLine S) n M.obj),
    WordComparison l E n
      (c.pull l E n (ProjectiveLine S ↘ S)
        (c.push l E n (ProjectiveLine S ↘ S) (originWord l E n p.classes.base o)))
      (c.push l E n (Etale.projectiveLineDiagonalProjection S (!a))
        (c.pull l E n (Etale.projectiveLineDiagonalProjection S a)
          (originWord l E n p.classes.base o)))
      (p.exchangeAt l E a M.obj)
      (EtaleWords.exchange (levelRing l E n) S a (DerivedCategory.Plus.ι.obj o.witness.complex))
  diagonal_pull : ∀ (a : Bool) (M : C l E p.classes.base (ProjectiveLine S))
    (o : SpTowerShriek.Origin l E p.classes.base (ProjectiveLine S) n M.obj),
    WordComparison l E n
      (c.pull l E n (diagonalImmersion S)
        (c.pull l E n (Etale.projectiveLineDiagonalProjection S a)
          (originWord l E n p.classes.base o)))
      (originWord l E n p.classes.base o)
      ((p.diagonalPull l E (Etale.projectiveLineDiagonalProjection S a)
        (diagonalIdentity S a)).hom.app M.obj)
      ((EtaleWords.diagonalPull (levelRing l E n) S a).hom.app
        (DerivedCategory.Plus.ι.obj o.witness.complex))
  source : ∀ (a : Bool) (M : C l E p.classes.base (ProjectiveLine S))
    (o : SpTowerShriek.Origin l E p.classes.base (ProjectiveLine S) n M.obj),
    WordComparison l E n (originWord l E n p.classes.base o)
      (c.push l E n (Etale.projectiveLineDiagonalProjection S a)
        (c.push l E n (diagonalImmersion S) (originWord l E n p.classes.base o)))
      (p.sourceUnitAt l E a M.obj)
      (EtaleWords.sourceUnit (levelRing l E n) S a (DerivedCategory.Plus.ι.obj o.witness.complex))

end AlgebraicGeometry.ProEtale.SpTowerP1
