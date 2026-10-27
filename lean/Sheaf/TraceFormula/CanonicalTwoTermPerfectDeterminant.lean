/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.TraceFormula.TwoTermPerfectDeterminant
public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import Sheaf.AlgebraicGeometry.LciCotangentPresentation

import Sheaf.TraceFormula.TwoTermPerfectTorWindow
import Sheaf.TraceFormula.TwoTermDeterminantPullbackCoherence
import Sheaf.TraceFormula.AffineTwoTermDeterminant
import Sheaf.TraceFormula.TwoTermDeterminantAffineDescent

/-! # Canonical exterior and pullback comparisons for two-term determinants

Source: Stacks Project, Tags 0FJI, 0FJM, 0FJX and 0FJY.
(blueprint: lem-trf-two-term-perfect-determinant).

The existing determinant record does not constrain its exterior-model identifications
on general quasi-isomorphisms. The predicate below supplies the exact-cone normalization
and fixes its pullback comparisons on finite locally free representatives.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The degree-minus-one component of a map between the actual double complexes,
transported along Mathlib's specified double-complex identifications.
Source: Stacks, Tags 0FJI and 0FJM
(blueprint: lem-trf-two-term-perfect-determinant). -/
def TwoTermDeterminantModel.negativeMap {X : Scheme.{u}}
    (P Q : TwoTermDeterminantModel X) (q : P.complex ⟶ Q.complex) : P.neg ⟶ Q.neg :=
  (HomologicalComplex.doubleXIso₀ P.differential (c := ComplexShape.up ℤ)
    (i₀ := -1) (i₁ := 0) (by decide)).inv ≫ q.f (-1) ≫
      (HomologicalComplex.doubleXIso₀ Q.differential (c := ComplexShape.up ℤ)
        (i₀ := -1) (i₁ := 0) (by decide)).hom

/-- The degree-zero component of the same chain map in the displayed model terms.
Source: Stacks, Tags 0FJI and 0FJM
(blueprint: lem-trf-two-term-perfect-determinant). -/
def TwoTermDeterminantModel.zeroMap {X : Scheme.{u}}
    (P Q : TwoTermDeterminantModel X) (q : P.complex ⟶ Q.complex) :
    P.nonneg ⟶ Q.nonneg :=
  (HomologicalComplex.doubleXIso₁ P.differential (c := ComplexShape.up ℤ)
    (i₀ := -1) (i₁ := 0) (by decide) (by decide)).inv ≫ q.f 0 ≫
      (HomologicalComplex.doubleXIso₁ Q.differential (c := ComplexShape.up ℤ)
        (i₀ := -1) (i₁ := 0) (by decide) (by decide)).hom

/-- The negative term map of a termwise pullback comparison, in the displayed terms.
The source term uses ordinary tensor pullback, with no choice of its identifications.
Source: Stacks, Tags 0FJY and 06YJ
(blueprint: lem-trf-two-term-perfect-determinant). -/
def TwoTermDeterminantModel.pullbackNegativeMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (P : TwoTermDeterminantModel X) (Q : TwoTermDeterminantModel Y)
    (q : CotangentPresentation.pullbackComplex g P.complex ⟶ Q.complex) :
    (tensorPullback g).obj P.neg ⟶ Q.neg :=
  (tensorPullback g).map
    (HomologicalComplex.doubleXIso₀ P.differential (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide)).inv ≫ q.f (-1) ≫
        (HomologicalComplex.doubleXIso₀ Q.differential (c := ComplexShape.up ℤ)
          (i₀ := -1) (i₁ := 0) (by decide)).hom

/-- The degree-zero term map of a termwise pullback comparison.
Source: Stacks, Tags 0FJY and 06YJ
(blueprint: lem-trf-two-term-perfect-determinant). -/
def TwoTermDeterminantModel.pullbackZeroMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (P : TwoTermDeterminantModel X) (Q : TwoTermDeterminantModel Y)
    (q : CotangentPresentation.pullbackComplex g P.complex ⟶ Q.complex) :
    (tensorPullback g).obj P.nonneg ⟶ Q.nonneg :=
  (tensorPullback g).map
    (HomologicalComplex.doubleXIso₁ P.differential (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide) (by decide)).inv ≫ q.f 0 ≫
        (HomologicalComplex.doubleXIso₁ Q.differential (c := ComplexShape.up ℤ)
          (i₀ := -1) (i₁ := 0) (by decide) (by decide)).hom

/-- Canonicity of the existing determinant data, independent of any adjunction line or
cotangent complex. For every quasi-isomorphism of displayed models, `modelIso` transports
the functor's map to the signed exact-cone determinant formula. Thus model comparisons
are fixed on changes of frame, contractible summands and their good-diagram composites.
For every termwise pullback identification, `pullbackIso` transports to extension of
scalars on the dual-first pure wedge. The derived identification is fixed by the original
K-flat counit, so no arbitrary derived map can absorb a scalar. All schemes, models,
chain maps and scheme morphisms are quantified; no regular-presentation restriction or
Noetherian hypothesis occurs. The algebraic predicates are the shared exact-cone and
pure-wedge predicates, without invoking an adjunction-system existence theorem.
Source: Stacks, Tags 0FJI, 0FJM, 0FJX and 0FJY
(blueprint: lem-trf-two-term-perfect-determinant). -/
structure TwoTermPerfectDeterminantData.IsCanonical
    (T : TwoTermPerfectDeterminantData.{u, w}) : Prop where
  model : ∀ (X : Scheme.{u}) (P Q : TwoTermDeterminantModel X)
    (q : P.complex ⟶ Q.complex) (e : DerivedCategory.Q.obj P.complex ≅
      DerivedCategory.Q.obj Q.complex), e.hom = DerivedCategory.Q.map q →
    ∀ hr : P.negRank + Q.nonnegRank = Q.negRank + P.nonnegRank,
      IsFlatLCIDeterminantComparison P.neg Q.neg P.nonneg Q.nonneg
        P.negRank Q.negRank P.nonnegRank Q.nonnegRank hr
        P.differential Q.differential (P.negativeMap Q q) (P.zeroMap Q q)
        ((T.modelIso P).symm ≪≫
          twoTermDeterminantIso (T.functor X) (T.model_mem P) (T.model_mem Q) e ≪≫
            T.modelIso Q)
  pullback : ∀ (X Y : Scheme.{u}) (g : Y ⟶ X)
    (P : TwoTermDeterminantModel X) (Q : TwoTermDeterminantModel Y)
    (q : CotangentPresentation.pullbackComplex g P.complex ⟶ Q.complex)
    (e : (derivedPullback g).obj (DerivedCategory.Q.obj P.complex) ≅
      DerivedCategory.Q.obj Q.complex),
    e.hom = CotangentPresentation.pullbackCounit g P.complex ≫ DerivedCategory.Q.map q →
    IsIso (P.pullbackNegativeMap g Q q) → IsIso (P.pullbackZeroMap g Q q) →
    ∀ (ha : P.negRank = Q.negRank) (hn : P.nonnegRank = Q.nonnegRank),
      IsFlatLCIPullbackDeterminantComparison g P.neg P.nonneg Q.neg Q.nonneg
        P.negRank Q.negRank P.nonnegRank Q.nonnegRank ha hn
        (P.pullbackNegativeMap g Q q) (P.pullbackZeroMap g Q q)
        ((tensorPullback g).mapIso (T.modelIso P).symm ≪≫
          T.pullbackIso g _ (T.model_mem P) ≪≫
            twoTermDeterminantIso (T.functor Y)
              (T.pullback_mem g _ (T.model_mem P)) (T.model_mem Q) e ≪≫ T.modelIso Q)

/-- The determinant of two-term perfect objects, with its canonical exterior-model
and arbitrary-pullback normalizations. This repairs the original interface, whose
unconstrained `modelIso` fields did not express the word "canonically" in the node.
Source: Stacks, Tags 0FJI, 0FJM, 0FJX and 0FJY
(blueprint: lem-trf-two-term-perfect-determinant).

Proof (the dependency node's four steps):
1. Apply [lem-trf-two-term-perfect-tor-window]. Its local finite free models give the
Tor-window equivalence, membership of every displayed model and zero, and preservation
under arbitrary derived pullback.
2. Apply [lem-trf-two-term-determinant-pullback-coherence] to the original K-flat counits.
This gives the fixed derived identity/composition comparisons and their unit laws.
3. Apply [lem-trf-affine-two-term-determinant]: good diagrams express a derived
isomorphism by surjective quasi-isomorphisms. Their kernel-first wedge contractions
compose through fibre products and are independent of the diagram. In the exact cone
ordered as (negative target, degree-zero source), the contraction is precisely
IsFlatLCIDeterminantComparison, with sign (-1)^(a*(b+1)). On a termwise scalar extension
the same calculation sends a dual basis wedge tensor a basis wedge to its pulled-back
expression, which is IsFlatLCIPullbackDeterminantComparison; the derived map is the
K-flat counit followed by the localized chain map. Apply
[lem-trf-two-term-determinant-affine-descent] to glue these functors and equations.
The equations hold on trivializing opens, so sheaf uniqueness makes them global;
neither affine intersections nor separatedness is needed.
4. Assemble the original record with these same model and pullback isomorphisms.
The normalized unit law is derivedId_normalization. The two equations just established
give IsCanonical. This supplies the normalized functor independently of any adjunction
comparison, on all schemes including the empty scheme and on zero-rank models.
-/
theorem exists_canonicalTwoTermPerfectDeterminantData
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    (∀ (X : Scheme.{u}) (L : schemeDerivedCategory X),
      isTwoTermPerfect X L ↔ Scheme.IsPerfect X L ∧
        ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
          i < -1 ∨ 0 < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
            (L ⊗ (DerivedCategory.singleFunctor _ 0).obj M))) ∧
      ∃ T : TwoTermPerfectDeterminantData.{u, w}, T.IsCanonical := by
  sorry

end AlgebraicGeometry
