/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.CondensedQbarCoefficientConstruction
public import Sheaf.Paper.GeometricFieldProEtaleEvaluation

/-! # Compatibility of bounded coefficient constructions
Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The specified abelian comparison preserves the scalar action on every module.

Source: Bhatt--Scholze, Example 4.1.10; RefactorInstruction, Section 4,
geometric-fiber comparison, steps 1--3
(blueprint: lem-weil-pbc-condensed-qbar-field-evaluation-linearity).

Proof in words: the comparison is the inverse-image adjunction unit followed by
restriction along the canonical terminal-object comparison. Both respect the lax
monoidal maps: use monoidality of the adjunction unit, then naturality of the
restriction map for the tensor action and tensor unit. Apply this identity to the
internal action A tensor M -> M. It identifies the evaluated source action with
the evaluated inverse-image action, with coefficient transported by the evaluation
comparison on A and by condensedPullbackHom. To identify this coefficient map in
the fixed Qbar_l coordinates, precompose with the invertible globalCoefficientIso
and the bounded-presheaf unit at the terminal object. A bounded function on Spec(K)
is constant, and its pullback to Spec(K') has the same value. The normalized
profinite-test formula globalCoefficientIso_test identifies both comparisons;
fieldUnitIso cancels the units, and boundedPointIso evaluates the same constant.
The resulting coefficient square commutes since all precomposed maps are
surjective. Restriction along inv(condensedPullbackHom) cancels that coefficient
map, so the ordinary module action and ULift restriction give the stated scalar
identity, for every module and every scalar. Identity embeddings, zero modules,
and transcendental extensions satisfy the same argument; no algebraicity is used.
-/
theorem condensedQbar_field_evaluation_linear (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K')
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))))
    (r : PadicAlgCl ℓ) :
    let f := Spec.map (CommRingCat.ofHom i)
    let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
    let H := upperStar Ab.{u + 1} f
    let α := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f
    let N := ((H.mapMod A ⋙ Mod.comap (inv α)) ⋙
      CondensedQbarGeometricEvaluation.fieldFiber K' ℓ).obj M
    (geometricFieldEvaluationComparison f Ab).app M.X ≫ N.smul r =
      ((CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj M).smul r ≫
        (geometricFieldEvaluationComparison f Ab).app M.X := by sorry

end AlgebraicGeometry.ProEtale
