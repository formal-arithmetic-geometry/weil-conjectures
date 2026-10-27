/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.SixFunctors.ScalarSixCtfGenerators

/-! # Integral and field generation in the scalar-perfect presentation.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (1), generators.
(blueprint: lem-sfb-scalar-six-nonfinite-generation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

/-- Integral and field generation in the scalar-perfect presentation.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (1), generators.
(blueprint: lem-sfb-scalar-six-nonfinite-generation).

Proof in words: first use the displayed coefficient isomorphism to move to its native
presentation, with the exact monoidal equivalence on modules and derived categories.
For integers of a finite extension use integralTensorShriek_generated. The integral
constant-model comparison identifies its bounded constructibility hypothesis with the
present one. Its point complexes have finite free terms and scalar-matrix
differentials; evaluating the matrices at the point and extending constants gives
bounded finite-free scalar complexes with the same realized complexes. Thus each
native generator is a scalar-perfect generator. For finite extensions of Q_ell and the algebraic
closure use coefficientHeart_generation. Each lisse module is finite free on its
specified cover, so the degree-zero complex of that free scalar module supplies a
scalar-perfect model. The ordinary exact extension and its derived extension agree
with the stated open-then-closed derived composite. Rotate the finitely many cone
triangles into extensions, replace finite direct sums by split extensions, and collect
retracts at the end. Z_ell and Q_ell are the bottom finite subextension cases. Transport
back across the given isomorphism. No completed derived category or infinite
coproduct enters the construction; zero and empty cases use rank zero. -/
theorem sfbNonfiniteScalarGeneration (ell : ℕ) [Fact ell.Prime]
    {Λ : ScalarSixRing.{u}}
    (hΛ : Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ell])) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ell])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
    (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
      ).retractClosure K.obj := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
