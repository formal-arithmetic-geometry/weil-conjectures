/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompleteCompactificationLimitSupport

/-! # Normalized scalar data for strict compactification systems
Source: blueprint direct-image proof, paragraph (2).
(blueprint: lem-sp-compactification-scalar-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The coefficient presentations and the ordinary and derived scalar squares.

Proof. Use the completed coefficient projections and their pullback compatibility to
obtain the scalar change squares. Transport the reduction/limit adjunction of
SequenceProjection.pushforwardLimitProjections through the recorded exact coefficient
section equivalences. Its tensor generators and counit identify the finite evaluations
and fix the unit-projection equation. The two recorded section presentations have the
identity comparison on their underlying modules, giving the evaluation isomorphisms.
For open extension, the scalar comparison is the identity on each extension summand;
semilinear transitions commute with this identity before exact localization. For direct
image, apply diagramRingRestrictionPushforward to the coefficient projections and
transport its unique comparison through the same section equivalences. Its ordinary
comparison is the identity on sections, hence has the stated finite normalization.
Invert its derived comparison: its universal composition-unit identity becomes precisely
IsPushScalarNormalized. These constructions take place on strict systems and complexes,
so they preserve all quotient transitions, before taking any inverse limit.
Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
sk-prop-sp-integral-adjunction-direct-image.proof.md, paragraph (2);
parent node proof steps 1 and 2; Stacks 03DI, 03D7, 0D6E.
(blueprint: lem-sp-compactification-scalar-data). -/
theorem compactificationScalarData
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (D : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T)
    (r : ∀ T : Scheme.{u}, SpReductionTower l E T (D T)) :
    ∃ (h : ScalarSquares l E)
      (a : ∀ T : Scheme.{u}, LimitPresentation l E T (D T) (r T))
      (v : ∀ T : Scheme.{u}, Evaluation l E b T (D T)),
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f)
      (_ : CompactSpace X) (_ : QuasiSeparatedSpace X)
      (_ : CompactSpace c.Z) (_ : QuasiSeparatedSpace c.Z)
      (_ : CompactSpace Y) (_ : QuasiSeparatedSpace Y)
      (_ : ∀ x : X, IsUnit (l : X.residueField x))
      (_ : ∀ x : c.Z, IsUnit (l : c.Z.residueField x))
      (_ : ∀ x : Y, IsUnit (l : Y.residueField x)) (_ : QuasiCompact c.i),
    ∃ (openOrdinary : forgetting l E X (D X) ⋙ fixedOpenOrd l E c.i ≅
    ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z (D c.Z)),
    ∃ (pushOrdinary : forgetting l E c.Z (D c.Z) ⋙ fixedPushOrd l E c.g ≅
    ordinaryTowerPush l E b o c.g ⋙ forgetting l E Y (D Y)),
    ∃ (pushDerived : forgetDerived l E c.Z (D c.Z) (r c.Z) (a c.Z) ⋙
      (fixedPushOrd l E c.g).rightDerivedFunctor ≅
    towerPush l E b o c.g (D c.Z) (D Y) ⋙ forgetDerived l E Y (D Y) (r Y) (a Y)),
    (∀ (N : spCoefficientTowers l E X) (n : ℕ),
    (openOrdinary.hom.app N).app (op n) ≫
        (spCompletedEllRestriction l E c.Z n).map
          ((ordinaryOpenEvaluation l E b o c.i (D X) (D c.Z) (v X) (v c.Z) n).hom.app N) =
      (ordinaryOpenScalar l E b h c.i n).hom.app
        ((spCoefficientEvaluation l E X (D X).equivalence n).obj N)) ∧
    (∀ (N : spCoefficientTowers l E c.Z) (n : ℕ),
    (pushOrdinary.hom.app N).app (op n) ≫
        (spCompletedEllRestriction l E Y n).map
          ((ordinaryPushEvaluation l E b o c.g (D c.Z) (D Y) (v c.Z) (v Y) n).hom.app N) =
      (ordinaryPushScalar l E h c.g n).hom.app
        ((spCoefficientEvaluation l E c.Z (D c.Z).equivalence n).obj N)) ∧
    IsPushScalarNormalized l E b o c.g (D c.Z) (D Y) (r c.Z) (r Y) (a c.Z) (a Y)
    pushOrdinary pushDerived := by sorry

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
