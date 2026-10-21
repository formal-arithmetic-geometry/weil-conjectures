/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGenericStratumMate
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Evaluation coherence of immersion internal-Hom exchange

Source: Stacks Project, Tag 08J9 and equation 08J8; the cartesian mate calculation in
blueprint thm-weil-etale-geometric-biduality, proof paragraph 4
(blueprint: lem-sf-etale-generic-evaluation-coherence).

The specified isomorphisms are bound with exactly the tensor-transpose characterization
of `immersionInternalHomIso`, at the two fixed pairs of inputs.
The composite below uses ordinary unbounded constant-coefficient etale derived categories.
The final equality identifies its first Hom input by the canonical extension-by-zero
base-change arrow. No inverse of direct-image exchange or exceptional comparison occurs.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The five-arrow composite: pulled-back stratum isomorphism, ordinary exchange,
transpose of pulled-back evaluation, Hom of the exceptional comparison, and inverse
primed stratum isomorphism. Source: Stacks Tag 08J9, cartesian mate calculation
(blueprint: lem-sf-etale-generic-evaluation-coherence).
The Hom pullback arrow is written using the existing tensor-Hom adjunction and canonical
tensor comparison. It is the same evaluation transpose as `inverseImageHomExchange` in
the downstream generic-exchange module, which cannot be imported here without a cycle. -/
noncomputable def immersionEvaluationComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X S' U' X' : Scheme.{u}}
    {i : S ⟶ U} {j : U ⟶ X} {i' : S' ⟶ U'} {j' : U' ⟶ X'}
    {gS : S' ⟶ S} {gU : U' ⟶ U} {gX : X' ⟶ X}
    [IsClosedImmersion i] [IsOpenImmersion j]
    [IsClosedImmersion i'] [IsOpenImmersion j']
    (hi : IsPullback gS i' i gU) (hj : IsPullback gU j' j gX)
    (P : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    (a : (L((gS)^*[ModuleCat.{u + 1} A])).obj
        ((immersionUpperShriek A i j).obj M) ⟶
      (immersionUpperShriek A i' j').obj ((L((gX)^*[ModuleCat.{u + 1} A])).obj M))
    (θ : ((derivedHom (ModuleCat.{u + 1} A) X).obj
        (op ((immersionLowerShriek A i j).obj P))).obj M ≅
      (R((i ≫ j)_*[ModuleCat.{u + 1} A])).obj
        (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
          ((immersionUpperShriek A i j).obj M)))
    (θ' : ((derivedHom (ModuleCat.{u + 1} A) X').obj
        (op ((immersionLowerShriek A i' j').obj
          ((L((gS)^*[ModuleCat.{u + 1} A])).obj P)))).obj
            ((L((gX)^*[ModuleCat.{u + 1} A])).obj M) ≅
      (R((i' ≫ j')_*[ModuleCat.{u + 1} A])).obj
        (((derivedHom (ModuleCat.{u + 1} A) S').obj
          (op ((L((gS)^*[ModuleCat.{u + 1} A])).obj P))).obj
            ((immersionUpperShriek A i' j').obj
              ((L((gX)^*[ModuleCat.{u + 1} A])).obj M)))) :
    (L((gX)^*[ModuleCat.{u + 1} A])).obj
        (((derivedHom (ModuleCat.{u + 1} A) X).obj
          (op ((immersionLowerShriek A i j).obj P))).obj M) ⟶
      ((derivedHom (ModuleCat.{u + 1} A) X').obj
        (op ((immersionLowerShriek A i' j').obj
          ((L((gS)^*[ModuleCat.{u + 1} A])).obj P)))).obj
            ((L((gX)^*[ModuleCat.{u + 1} A])).obj M) :=
  (L((gX)^*[ModuleCat.{u + 1} A])).map
      θ.hom ≫
    (derivedBaseChangeMap (ModuleCat.{u + 1} A)
      (hi.toCommSq.vert_comp hj.toCommSq)).app
        (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
          ((immersionUpperShriek A i j).obj M)) ≫
    (R((i' ≫ j')_*[ModuleCat.{u + 1} A])).map
      ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
          ((L((gS)^*[ModuleCat.{u + 1} A])).obj P)).homEquiv _ _
        ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) gS P
            (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
              ((immersionUpperShriek A i j).obj M))).inv ≫
          (L((gS)^*[ModuleCat.{u + 1} A])).map
            ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) P).counit.app
              ((immersionUpperShriek A i j).obj M)))) ≫
    (R((i' ≫ j')_*[ModuleCat.{u + 1} A])).map
      (((derivedHom (ModuleCat.{u + 1} A) S').obj
        (op ((L((gS)^*[ModuleCat.{u + 1} A])).obj P))).map a) ≫
    θ'.inv

/-- The immersion exchange composite transposes to pulled-back evaluation, and therefore
is the canonical Hom pullback comparison after identifying its first input by `b_P`.
Source: Stacks Tag 08J9, equation 08J8; blueprint geometric biduality, proof paragraph 4
(blueprint: lem-sf-etale-generic-evaluation-coherence).

Proof plan:
1. Put F = Rs_!, R = Rs_*, q = s^*, T = gX^*, U = gS^*, N = Rs^! M,
H = RHom(P,N), C = RHom(FP,M). Let t : qC → H be the ordinary adjoint of theta_s.
The normalization in lem-sf-etale-generic-stratum-mate identifies evaluation with
projection, F of (t tensor identity), F of evaluation, then the exceptional counit.
2. Expand the ordinary exchange as the adjunction mate of the inverse-image square
(def-kun-unbounded-exchange). Its adjoint after T(theta_s) is U(t) composed with
that square comparison. No invertibility of ordinary exchange is used.
3. The defining tensor transpose of the inner Hom pullback comparison and naturality
of evaluation identify the next adjoint's transpose with a composed with U of the
transpose of t, preceded by the canonical tensor and square comparisons. Use
lem-sf-ringed-derived-closed-symmetric-monoidal and
lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
4. Apply the primed stratum-mate normalization to this adjoint. The transpose of the
five-arrow composite is primed projection, primed extension by zero of this map,
then the primed exceptional counit, for arbitrary unbounded test complexes.
5. Use the assumed projection base-change equality and naturality of b to replace
primed projection and the pulled-back tensor square by T of the original projection.
The square and tensor identifications agree under composition by
lem-sfb-ringed-derived-monoidal-comparisons.
6. Apply the exceptional counit identity hCounit, then the evaluation identity of
step 1. This is the first equality. Injectivity of tensor-Hom transposition gives
the second equality, with contravariance in b_P making its Hom inputs identical.
Only canonical tensor and extension-by-zero isomorphisms are identified; neither
the ordinary exchange, a, nor the inner Hom comparison is assumed invertible. -/
theorem immersionEvaluationCoherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X S' U' X' : Scheme.{u}}
    {i : S ⟶ U} {j : U ⟶ X} {i' : S' ⟶ U'} {j' : U' ⟶ X'}
    {gS : S' ⟶ S} {gU : U' ⟶ U} {gX : X' ⟶ X}
    [IsClosedImmersion i] [IsOpenImmersion j]
    [IsClosedImmersion i'] [IsOpenImmersion j']
    (hi : IsPullback gS i' i gU) (hj : IsPullback gU j' j gX)
    (P : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    (a : (L((gS)^*[ModuleCat.{u + 1} A])).obj
        ((immersionUpperShriek A i j).obj M) ⟶
      (immersionUpperShriek A i' j').obj ((L((gX)^*[ModuleCat.{u + 1} A])).obj M))
    (θ : ((derivedHom (ModuleCat.{u + 1} A) X).obj
        (op ((immersionLowerShriek A i j).obj P))).obj M ≅
      (R((i ≫ j)_*[ModuleCat.{u + 1} A])).obj
        (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
          ((immersionUpperShriek A i j).obj M)))
    (θ' : ((derivedHom (ModuleCat.{u + 1} A) X').obj
        (op ((immersionLowerShriek A i' j').obj
          ((L((gS)^*[ModuleCat.{u + 1} A])).obj P)))).obj
            ((L((gX)^*[ModuleCat.{u + 1} A])).obj M) ≅
      (R((i' ≫ j')_*[ModuleCat.{u + 1} A])).obj
        (((derivedHom (ModuleCat.{u + 1} A) S').obj
          (op ((L((gS)^*[ModuleCat.{u + 1} A])).obj P))).obj
            ((immersionUpperShriek A i' j').obj
              ((L((gX)^*[ModuleCat.{u + 1} A])).obj M))))
    (hθ : ∀ (C : DerivedCategoryModule A X)
      (f : C ⟶ (R((i ≫ j)_*[ModuleCat.{u + 1} A])).obj
        (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
          ((immersionUpperShriek A i j).obj M))),
      derivedTensorHom (ModuleCat.{u + 1} A) (f ≫ θ.inv)
          (𝟙 ((immersionLowerShriek A i j).obj P)) ≫
        immersionHomEvaluation A X ((immersionLowerShriek A i j).obj P) M =
      immersionProjectionMap A i j C P ≫
        (immersionLowerShriek A i j).map
          (derivedTensorHom (ModuleCat.{u + 1} A)
            (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
              (i ≫ j)).homEquiv C
                (((derivedHom (ModuleCat.{u + 1} A) S).obj (op P)).obj
          ((immersionUpperShriek A i j).obj M))).symm f) (𝟙 P)) ≫
        (immersionLowerShriek A i j).map
          (immersionHomEvaluation A S P ((immersionUpperShriek A i j).obj M)) ≫
        (immersionLowerUpperShriekAdjunction A i j).counit.app M)
    (hθ' : ∀ (C : DerivedCategoryModule A X')
      (f : C ⟶ (R((i' ≫ j')_*[ModuleCat.{u + 1} A])).obj
        (((derivedHom (ModuleCat.{u + 1} A) S').obj (op ((L((gS)^*[ModuleCat.{u + 1} A])).obj
          P))).obj
          ((immersionUpperShriek A i' j').obj ((L((gX)^*[ModuleCat.{u + 1} A])).obj M)))),
      derivedTensorHom (ModuleCat.{u + 1} A) (f ≫ θ'.inv)
          (𝟙 ((immersionLowerShriek A i' j').obj ((L((gS)^*[ModuleCat.{u + 1} A])).obj P))) ≫
        immersionHomEvaluation A X' ((immersionLowerShriek A i' j').obj ((L((gS)^*[ModuleCat.{u + 1}
          A])).obj P)) ((L((gX)^*[ModuleCat.{u + 1} A])).obj M) =
      immersionProjectionMap A i' j' C ((L((gS)^*[ModuleCat.{u + 1} A])).obj P) ≫
        (immersionLowerShriek A i' j').map
          (derivedTensorHom (ModuleCat.{u + 1} A)
            (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
              (i' ≫ j')).homEquiv C
                (((derivedHom (ModuleCat.{u + 1} A) S').obj (op ((L((gS)^*[ModuleCat.{u + 1}
                  A])).obj P))).obj
          ((immersionUpperShriek A i' j').obj ((L((gX)^*[ModuleCat.{u + 1} A])).obj M)))).symm f) (𝟙
            ((L((gS)^*[ModuleCat.{u + 1} A])).obj P))) ≫
        (immersionLowerShriek A i' j').map
          (immersionHomEvaluation A S' ((L((gS)^*[ModuleCat.{u + 1} A])).obj P)
            ((immersionUpperShriek A i' j').obj ((L((gX)^*[ModuleCat.{u + 1} A])).obj M))) ≫
        (immersionLowerUpperShriekAdjunction A i' j').counit.app ((L((gX)^*[ModuleCat.{u + 1}
          A])).obj M))
    (hCounit : immersionLowerShriekBaseChangeMap A hi hj
          ((immersionUpperShriek A i j).obj M) ≫
        (immersionLowerShriek A i' j').map a ≫
        (immersionLowerUpperShriekAdjunction A i' j').counit.app
          ((L((gX)^*[ModuleCat.{u + 1} A])).obj M) =
      (L((gX)^*[ModuleCat.{u + 1} A])).map
        ((immersionLowerUpperShriekAdjunction A i j).counit.app M))
    (hProjection : ∀ (C : DerivedCategoryModule A X) (Q : DerivedCategoryModule A S),
      (L((gX)^*[ModuleCat.{u + 1} A])).map (immersionProjectionMap A i j C Q) ≫
          immersionLowerShriekBaseChangeMap A hi hj
            (((derivedTensor (ModuleCat.{u + 1} A) S).obj
              ((L((i ≫ j)^*[ModuleCat.{u + 1} A])).obj C)).obj Q) ≫
          (immersionLowerShriek A i' j').map
            (immersionProjectionBaseChangeTensorMap A hi hj C Q) =
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) gX).app C).app
            ((immersionLowerShriek A i j).obj Q) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X').obj
            ((L((gX)^*[ModuleCat.{u + 1} A])).obj C)).map
              (immersionLowerShriekBaseChangeMap A hi hj Q) ≫
          immersionProjectionMap A i' j'
            ((L((gX)^*[ModuleCat.{u + 1} A])).obj C)
            ((L((gS)^*[ModuleCat.{u + 1} A])).obj Q)) :
    derivedTensorHom (ModuleCat.{u + 1} A)
        (𝟙 ((L((gX)^*[ModuleCat.{u + 1} A])).obj
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op ((immersionLowerShriek A i j).obj P))).obj
            M))) (immersionLowerShriekBaseChangeMap A hi hj P) ≫
      derivedTensorHom (ModuleCat.{u + 1} A)
        (immersionEvaluationComparison A hi hj P M a θ θ') (𝟙 ((immersionLowerShriek A i' j').obj
            ((L((gS)^*[ModuleCat.{u + 1} A])).obj P))) ≫
      immersionHomEvaluation A X' ((immersionLowerShriek A i' j').obj
            ((L((gS)^*[ModuleCat.{u + 1} A])).obj P)) ((L((gX)^*[ModuleCat.{u + 1} A])).obj M) =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) gX
      (((derivedHom (ModuleCat.{u + 1} A) X).obj (op ((immersionLowerShriek A i j).obj P))).obj M)
        ((immersionLowerShriek A i j).obj P)).inv ≫
      (L((gX)^*[ModuleCat.{u + 1} A])).map
        (immersionHomEvaluation A X ((immersionLowerShriek A i j).obj P) M) ∧
    immersionEvaluationComparison A hi hj P M a θ θ' ≫
      ((derivedHom (ModuleCat.{u + 1} A) X').map
        (immersionLowerShriekBaseChangeMap A hi hj P).op).app
          ((L((gX)^*[ModuleCat.{u + 1} A])).obj M) =
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) ((L((gX)^*[ModuleCat.{u + 1} A])).obj
      ((immersionLowerShriek A i j).obj P))).homEquiv _ _
      ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) gX
        ((immersionLowerShriek A i j).obj P)
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op ((immersionLowerShriek A i j).obj P))).obj
          M)).inv ≫
        (L((gX)^*[ModuleCat.{u + 1} A])).map
          ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
            ((immersionLowerShriek A i j).obj P)).counit.app M)) := by
  sorry

end AlgebraicGeometry.Etale
