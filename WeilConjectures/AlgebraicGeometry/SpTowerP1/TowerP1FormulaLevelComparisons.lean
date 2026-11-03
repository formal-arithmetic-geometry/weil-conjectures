/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1ProjectionLevelComparisons
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1TensorCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleWords
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-formula-level-comparisons).

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

/-- The finite class and line comparisons used inside the displayed formulas.
These are equations for p.delta, p.trace and p.line2Iso, rather than a detached
assertion that a root-site comparison exists.
Source: Construction and Levels (blueprint: def-sp-p1-formula-level-comparisons). -/
structure ClassLevelComparisons (c : ProjectiveCoordinates l E n p)
    (hD : (diagonalImmersion S).ker.IsInvertible) : Prop where
  delta : WordComparison l E n
    (c.push l E n (diagonalImmersion S) (c.unitP l E n)) (c.lineW l E n)
    (p.delta l E)
    (EtaleWords.delta (levelRing l E n) (l ^ (n + 1))
      (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
      S hD (surfaceExponentUnit l n hS))
  trace : WordComparison l E n
    (c.push l E n (ProjectiveLine S ↘ S) (c.lineP l E n)) (c.unitS l E n)
    (p.trace l E) c.splitting.trace
  shifted_line : WordComparison l E n
    (c.pull l E n (Etale.projectiveLineDiagonalProjection S true) (c.lineP l E n))
    (c.lineW l E n) (p.line2Iso l E).hom
    (Etale.ordinaryFiniteShiftedLinePullback (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport
      (Etale.projectiveLineDiagonalProjection S true) (lineExponentUnit l n hS)).hom

/-- The two decisive finite equations, for the actual eta and epsilon words and for
EVERY retained etale-origin witness. The finite eta is the explicit diagonal word;
the finite epsilon is the explicit splitting-trace word.
Source: Levels (blueprint: def-sp-p1-formula-level-comparisons). -/
structure FormulaLevelComparisons (c : ProjectiveCoordinates l E n p)
    (d : Maps l E p) (hD : (diagonalImmersion S).ker.IsInvertible) : Prop where
  eta : ∀ (M : C l E p.classes.base (ProjectiveLine S))
    (o : SpTowerShriek.Origin l E p.classes.base (ProjectiveLine S) n M.obj),
    WordComparison l E n (originWord l E n p.classes.base o)
      (c.tensor l E n
        (c.pull l E n (ProjectiveLine S ↘ S)
          (c.push l E n (ProjectiveLine S ↘ S) (originWord l E n p.classes.base o)))
        (c.lineP l E n))
      (SpTowerP1.eta l E d M)
      (EtaleWords.eta (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
        S hD (surfaceExponentUnit l n hS) c.transport c.invertible o.witness.complex.obj)
  epsilon : ∀ (K : C l E p.classes.base S)
    (o : SpTowerShriek.Origin l E p.classes.base S n K.obj),
    WordComparison l E n
      (c.push l E n (ProjectiveLine S ↘ S)
        (c.tensor l E n
          (c.pull l E n (ProjectiveLine S ↘ S) (originWord l E n p.classes.base o))
          (c.lineP l E n)))
      (originWord l E n p.classes.base o)
      (SpTowerP1.epsilon l E d K)
      (EtaleWords.epsilon (levelRing l E n) (l ^ (n + 1)) (levelAnnihilates l E n)
        S (baseExponentUnit l n hS) c.transport c.splitting c.invertible o.witness.complex.obj)

end AlgebraicGeometry.ProEtale.SpTowerP1
