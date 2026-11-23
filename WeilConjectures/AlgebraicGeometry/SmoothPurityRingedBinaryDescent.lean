/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import Mathlib.CategoryTheory.Triangulated.Basic

/-! # Binary descent for ringed coefficient towers

Source: Stacks Project, Tag 08DG, lemma `glue` in `cohomology.tex`;
the strict-system refinement in the smooth-purity blueprint
(blueprint: lem-sp-ringed-tower-binary-descent).

Restriction and direct image are transported from the section-preserving
`SpTowerShriek.Geometry` of the actual small pro-etale topoi. Its `pull_eq`,
`push_eq` and adjunction normalization identify them with the geometric
semilinear operations; no free restriction or direct-image functor is supplied.
The overlap comparison is built from restriction composition. The triangle
arrows are the smaller-open adjunction units followed by the canonical
right-adjoint composition comparison, and by the given overlap map on the U side.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- The fixed support and Tor intervals used by the normalized-tower clause.
Source: the statement of `lem-sp-ringed-tower-binary-descent` in the smooth-purity
blueprint. -/
def spHasFixedBounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (C : spDerivedCoefficientTowers l E T D)
    (a b c d : ℤ) : Prop :=
  a ≤ b ∧ c ≤ d ∧ ∀ n : ℕ,
    (∀ i : ℤ, (i < a ∨ b < i) → IsZero
      ((@DerivedCategory.homologyFunctor
        (Scheme.proEtaleRingModules T
          (Scheme.proEtaleConstantRing T
            (Padic.coefficientExtensionIntegers l E ⧸
              spEllIdeal l E ^ (n + 1))))
        _ _ (HasDerivedCategory.standard _) i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj C))) ∧
    Scheme.HasProEtaleTorAmplitude T
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
      ((spDerivedCoefficientEvaluation l E T D n).obj C) c d

/-- The actual restriction functor transported from the section-normalized
semilinear tower calculus to the recorded coefficient-tower category.
Source: semilinear derived sections and section-preserving tower realization
(blueprint: lem-sp-ringed-tower-binary-descent). -/
abbrev spActualRestriction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y) :
    spDerivedCoefficientTowers l E X D_X ⥤
      spDerivedCoefficientTowers l E Y D_Y :=
  (spTowerShriekRealization l E b X D_X).functor ⋙
    SpTowerShriek.pull l E b (o.geometry f) ⋙
    (spTowerShriekRealization l E b Y D_Y).inverse

/-- The actual total right-derived direct image transported to the recorded
coefficient-tower category. Source: semilinear geometric direct image
(blueprint: lem-sp-ringed-tower-binary-descent). -/
abbrev spActualDirectImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y) :
    spDerivedCoefficientTowers l E Y D_Y ⥤
      spDerivedCoefficientTowers l E X D_X :=
  (spTowerShriekRealization l E b Y D_Y).functor ⋙
    SpTowerShriek.push l E b (o.geometry f) ⋙
    (spTowerShriekRealization l E b X D_X).inverse

/-- The actual open inverse-image/right-derived-image adjunction after transport
through the section-normalized coefficient equivalences. Source: the actual
semilinear geometric adjunction (blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y) :
    spActualRestriction l E b o f D_X D_Y ⊣
      spActualDirectImage l E b o f D_X D_Y :=
  ((spTowerShriekRealization l E b X D_X).toAdjunction.comp
    (SpTowerShriek.adjunction l E b (o.geometry f))).comp
    (spTowerShriekRealization l E b Y D_Y).symm.toAdjunction

/-- Composition of the actual restrictions, cancelling only the intermediate
section-preserving presentation. Source: the semilinear composition calculus
(blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualRestrictionComp
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y)
    (D_Z : SpCoefficientTowersAbelian l E Z) :
    spActualRestriction l E b o f D_X D_Y ⋙
        spActualRestriction l E b o g D_Y D_Z ≅
      spActualRestriction l E b o (g ≫ f) D_X D_Z :=
  let e := spTowerShriekRealization l E b X D_X
  let m := spTowerShriekRealization l E b Y D_Y
  let n := spTowerShriekRealization l E b Z D_Z
  let p := SpTowerShriek.pull l E b (o.geometry f)
  let q := SpTowerShriek.pull l E b (o.geometry g)
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (e.functor ⋙ p)
      (Functor.isoWhiskerRight m.counitIso q) ≪≫
      Functor.isoWhiskerLeft e.functor (o.comp g f)) n.inverse

/-- The canonical overlap comparison from restriction composition and the
pullback equality. Source: Stacks 08DG
(blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualOverlap
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X U V W : Scheme.{u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (wU : W ⟶ U) (wV : W ⟶ V)
    (hW : wU ≫ jU = wV ≫ jV)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_U : SpCoefficientTowersAbelian l E U)
    (D_V : SpCoefficientTowersAbelian l E V)
    (D_W : SpCoefficientTowersAbelian l E W) :
    spActualRestriction l E b o jU D_X D_U ⋙
        spActualRestriction l E b o wU D_U D_W ≅
      spActualRestriction l E b o jV D_X D_V ⋙
        spActualRestriction l E b o wV D_V D_W :=
  spActualRestrictionComp l E b o jU wU D_X D_U D_W ≪≫
    eqToIso (congrArg (fun f ↦ spActualRestriction l E b o f D_X D_W) hW) ≪≫
    (spActualRestrictionComp l E b o jV wV D_X D_V D_W).symm

/-- The direct-image compositor is the unique right-adjoint comparison of the
actual restriction compositor. Source: semilinear adjunction calculus
(blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualDirectComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y)
    (D_Z : SpCoefficientTowersAbelian l E Z) :
    spActualDirectImage l E b o g D_Y D_Z ⋙
        spActualDirectImage l E b o f D_X D_Y ≅
      spActualDirectImage l E b o (g ≫ f) D_X D_Z :=
  (((spActualAdjunction l E b o f D_X D_Y).comp
    (spActualAdjunction l E b o g D_Y D_Z)).ofNatIsoLeft
      (spActualRestrictionComp l E b o f g D_X D_Y D_Z)).rightAdjointUniq
        (spActualAdjunction l E b o (g ≫ f) D_X D_Z)

/-- The restriction-unit arrow into the image from a smaller open.
Source: Stacks 08DG (blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualRestrictionUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y)
    (D_Z : SpCoefficientTowersAbelian l E Z)
    (A : spDerivedCoefficientTowers l E Y D_Y) :
    (spActualDirectImage l E b o f D_X D_Y).obj A ⟶
      (spActualDirectImage l E b o (g ≫ f) D_X D_Z).obj
        ((spActualRestriction l E b o g D_Y D_Z).obj A) :=
  (spActualDirectImage l E b o f D_X D_Y).map
      ((spActualAdjunction l E b o g D_Y D_Z).unit.app A) ≫
    (spActualDirectComparison l E b o f g D_X D_Y D_Z).hom.app
      ((spActualRestriction l E b o g D_Y D_Z).obj A)

end AlgebraicGeometry.ProEtale
