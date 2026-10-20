/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.IntegralConstantModelHeart
public import Sheaf.Paper.IntegralHeartLocalModel
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Sheaf.Paper.IntegralHeartDualizable
import Sheaf.Paper.IntegralModels

/-!
# Structure of integral constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-lem-int-integral-heart/_section.md`, assertions (1)--(3), and its proof;
Stacks Project, Tags 099I, 09C2, 09C7, 09C4, 0990, 099Q, 099Y
(blueprint: sk-lem-int-integral-heart).

The coefficients are the completed continuous coefficient sheaf, and the ambient
category is the ordinary unbounded derived category of its internal module objects.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The integral constructible derived category is triangulated and stable under
standard truncations, with essentially small extension-closed abelian heart. Every
heart object has finite module models on a finite stratification, and its restrictions
and their duals have Tor amplitudes [-1,0] and [0,1] on those very strata.
Source: blueprint main-20261015, sk-lem-int-integral-heart, assertions (1)--(3)
(blueprint: sk-lem-int-integral-heart).

Proof (the four steps of the DAG node):
1. The finite-type integral-model setting of sk-lem-integral-models makes X Noetherian.
Apply det-lem-int-integral-heart-triangulated(1): the bounded constructible predicate
is closed under isomorphisms, triangulated, bounded, and stable under both truncations.
2. By sk-def-sfb-constructible, a module in degree zero belongs to Dbc exactly when
it is constructible. The fully faithful single functor identifies every degree-zero
object with its H^0. Apply det-lem-int-integral-heart-triangulated(2) for ambient
kernels and cokernels, abelianness, extension closure, and essential smallness.
3. Given a constructible C, place it in degree zero by step 2. Apply
 det-lem-int-integral-heart-local-model(1),(2) and take q = 0. Its same finite strata
and charts identify C with the completed realization of the finite scalar module
H^0 of the finite free complex. This allows torsion in that module.
4. On each of those strata, det-lem-int-integral-heart-dualizable gives the derived
dual and its evaluation and coevaluation satisfying both triangle identities, encoded
by ExactPairing. A finite module over the coefficient DVR has a finite free resolution
in degrees [-1,0]; flat completed scalar extension preserves it. Dualizing gives a
finite free complex in degrees [0,1]. These compute Tor against every module sheaf,
including torsion sheaves. In particular O_E/pi has derived dual (O_E/pi)[-1]. -/
theorem integral_constructible_heart
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsTriangulated
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ K, constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K →
      DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Full ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Faithful ∧
    (∀ K, (ObjectProperty.ι
        (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
        DerivedCategory.singleFunctor _ 0).essImage K ↔
      constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K ∧
      DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
    Nonempty (Abelian (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X)) ∧
    ObjectProperty.IsClosedUnderKernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderCokernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderExtensions
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    EssentiallySmall.{u + 1}
      (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ C : SmallAdicCompletion.Modules ℓ E X,
      IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X C →
      ∃ s : Scheme.FiniteLocallyClosedStratification X,
        (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
        ∀ a : Fin s.n,
          (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
            ∀ i : 𝒰.I₀,
              ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
                Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
                Nonempty ((CondensedRing.upperStar (integralHeartCoefficientRingObj ℓ E)
                    (𝒰.f i ≫ s.immersion a)).obj C ≅
                  (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)) ∧
          ∃ D : integralHeartDerivedCategory.{u} ℓ E (s.domain a),
            Nonempty (ExactPairing D
              ((DerivedCategory.singleFunctor _ 0).obj
                ((CondensedRing.upperStar (integralHeartCoefficientRingObj ℓ E)
                  (s.immersion a)).obj C))) ∧
            DerivedCategory.torAmplitudeIn _ (-1) 0
              ((DerivedCategory.singleFunctor _ 0).obj
                ((CondensedRing.upperStar (integralHeartCoefficientRingObj ℓ E)
                  (s.immersion a)).obj C)) ∧
            DerivedCategory.torAmplitudeIn _ 0 1 D) := by
  sorry

end AlgebraicGeometry.ProEtale
