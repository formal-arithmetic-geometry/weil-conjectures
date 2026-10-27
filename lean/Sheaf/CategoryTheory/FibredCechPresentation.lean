/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.CategoryTheory.FibredRelativeCech

/-! # Presentations of the relative Cech nerve

Source: Stacks Project, Tags 06X3 and 0040
(blueprint: def-sfb-fibred-cech-presentation).

The functor to tuples records all leaf projections and their comparisons with the root.
Its being an equivalence is the cone universal property of the iterated 2-product.
Omission comparisons retain this data up to natural isomorphism, rather than demanding
strict equality of functors between arbitrarily chosen representatives.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

/-- An iterated 2-product presentation, expressed by its universal common-target cone.
The equivalence condition says that every tuple cone is represented, uniquely up to
isomorphism, and every compatible arrow of cones lifts uniquely. Thus it retains
arrows and automorphisms, not only isomorphism classes. Degree zero includes `U`
via the cone `(u, f(u), id)` as well as its equivalent redundant tuple model.
Source: Stacks 06X3 and Categories 0040
(blueprint: def-sfb-fibred-cech-presentation). -/
structure FibredCechPresentation {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} (f : BasedFunctor U X) where
  /-- Chosen total category in degree `p`. -/
  level : ℕ → Type (max v w)
  /-- The morphism universe of each total category. -/
  category : ∀ p, Category.{v} (level p)
  /-- The universal cone, including its leaf arrows to the common target. -/
  flatten : ∀ p, @Functor (level p) (category p) (FibredCechTuple f (p + 1)) _
  /-- The universal property on both objects and arrows of cones. -/
  universal : ∀ p, (flatten p).IsEquivalence
  /-- Omission of the indicated leaf. -/
  face : ∀ p, Fin (p + 2) → @Functor (level (p + 1)) (category (p + 1))
    (level p) (category p)
  /-- Omission respects the universal cone, with its specified coefficient transport. -/
  omission : ∀ p j, face p j ⋙ flatten p ≅
    flatten (p + 1) ⋙ fibredCechTupleReindex f j.succAbove

attribute [instance] FibredCechPresentation.category

/-- Projection to the root of a presentation's universal cone.
Source: Stacks 06X3 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.projection {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f) (p : ℕ) :
    @Functor (P.level p) (P.category p) X.obj _ :=
  P.flatten p ⋙ fibredCechTupleProjection f (p + 1)

/-- Relative term, including the identity coefficient functor in augmented degree -1.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.term {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f) :
    ℕ → (X.objᵒᵖ ⥤ AddCommGrpCat.{max v w}) ⥤ (X.objᵒᵖ ⥤ AddCommGrpCat.{max v w})
  | 0 => 𝟭 _
  | p + 1 => fibredCechTerm (P.projection p)

/-- Pullback under each omission, using the root component of its cone comparison.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.coface {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f) (p : ℕ) (j : Fin (p + 2)) :
    P.term (p + 1) ⟶ P.term (p + 2) :=
  fibredCechPullback (P.projection p) (P.projection (p + 1)) (P.face p j)
      (isoWhiskerRight (P.omission p j) (fibredCechTupleProjection f (p + 1)))

/-- The augmentation is the unit of restriction followed by compatible-family direct image.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.augmentation {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f) : P.term 0 ⟶ P.term 1 :=
  ((P.projection 0).op.ranAdjunction AddCommGrpCat.{max v w}).unit

/-- Alternating differential, with the augmentation at the first index.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.differential {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f) : (n : ℕ) → P.term n ⟶ P.term (n + 1)
  | 0 => P.augmentation
  | p + 1 => ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • P.coface p j

/-- The common-target presentation, including the redundant singleton in degree zero.
Source: Stacks 06X3 (blueprint: def-sfb-fibred-cech-presentation). -/
def fibredTupleCechPresentation {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} (f : BasedFunctor U X) :
    FibredCechPresentation f where
  level p := FibredCechTuple f (p + 1)
  category _ := inferInstance
  flatten _ := 𝟭 _
  universal _ := inferInstance
  face _ j := fibredCechTupleReindex f j.succAbove
  omission _ _ := Iso.refl _

/-- The canonical restriction of compatible families along the universal cone.
Its inverse, when invertibility is proved, is the presentation comparison.
Source: Stacks 06X5 and 06X9 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.comparison {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f) : (n : ℕ) →
    (fibredTupleCechPresentation f).term n ⟶ P.term n
  | 0 => 𝟙 _
  | p + 1 => fibredCechPullback (fibredCechTupleProjection f (p + 1))
      (P.projection p) (P.flatten p) (Iso.refl _)

/-- The term functor restricted to abelian sheaf coefficients.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.restrictedTerm {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f) (n : ℕ) :=
  sheafToPresheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w} ⋙ P.term n

/-- The differential restricted to abelian sheaf coefficients.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.restrictedDifferential {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f) (n : ℕ) :
    P.restrictedTerm n ⟶ P.restrictedTerm (n + 1) :=
  whiskerLeft (sheafToPresheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w})
    (P.differential n)

/-- The augmented complex indexed starting at zero, given its differential-square law.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.nonnegativeComplex {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f)
    (hd : ∀ n : ℕ, P.restrictedDifferential n ≫ P.restrictedDifferential (n + 1) = 0) :
    CochainComplex (Sheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w} ⥤
      X.objᵒᵖ ⥤ AddCommGrpCat.{max v w}) ℕ :=
  CochainComplex.of P.restrictedTerm P.restrictedDifferential hd

/-- Extension by zero, placing the augmentation in integer degree -1.
All terms will be sheaves when the sheaf property in the comparison theorem is applied;
the fully faithful sheaf inclusion identifies this with the complex of abelian sheaves.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-cech-presentation). -/
def FibredCechPresentation.complex {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} {f : BasedFunctor U X}
    (P : FibredCechPresentation f)
    (hd : ∀ n : ℕ, P.restrictedDifferential n ≫ P.restrictedDifferential (n + 1) = 0) :
    CochainComplex (Sheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w} ⥤
      X.objᵒᵖ ⥤ AddCommGrpCat.{max v w}) ℤ :=
  (P.nonnegativeComplex hd).extend (ComplexShape.embeddingUpIntGE (-1))

end CategoryTheory
