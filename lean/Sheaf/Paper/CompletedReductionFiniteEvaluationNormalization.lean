/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.CompletedPullbackReductionData
public import Sheaf.Paper.FourCorners

import all Sheaf.Paper.CompletedPullbackReductionData
import all Sheaf.Paper.CompletedTowerPullback

/-! # Universal-counit normalized derived finite evaluation

Source: blueprint `main-20261015`, lemma-weil-pbc-completed-pullback-reduction, paragraph 2;
agent-written interface refinement of Stacks Project Tag 099N (proetale.tex,
lemma-pushforward-Noetherian-case), clause (5).
(blueprint: lem-weil-pbc-derived-finite-evaluation-normalization).

## Main statements

- `completedReductionFiniteEvaluation_normalized`: the completed coefficient map is the
  four-corners integral ring isomorphism, completed and strict-tower pullback are exact,
  the two universal-counit model maps are natural and invertible on K-flat complexes, and
  `completedReductionFiniteEvaluation` is the unique natural isomorphism with the
  representative normalization.

A natural number `n` denotes the positive exponent `n + 1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] completedTowerModulePullback_additive
attribute [local instance] completedReductionModuleTowerFunctor_additive

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The universal-counit normalized derived finite evaluation, with all its clauses.
Source: blueprint lemma-weil-pbc-completed-pullback-reduction, paragraph 2; Stacks Tags
099N (5), 098T, 097N, 04JC, 02MZ, 015F, 05S9, 06YS, 06YT, 06XN
(blueprint: lem-weil-pbc-derived-finite-evaluation-normalization).

Proof. Step 1: apply lem-weil-pbc-profinite-coefficient-inverse-image to the finite tower
`P_n`; its isomorphism `c` satisfies `π_{T',n} c = c_{g,n} g⁻¹ π_{T,n}`, the components
defining `c_g`; maps to the limit with equal projections agree, so `c_g = c`, which is
the four-corners integral map (use the square with identity vertical arrows).
Step 2: inverse image is exact (lem-trf-geometric-inverse-image-exact); extension along
the ring isomorphism `c_g` only relabels scalars, so `G` is exact; strict towers have
levelwise kernels and cokernels (lem-weil-tower-category-levelwise-abelian), so `G^Tow`
and evaluation are exact; `g_n^*` is exact (prop-weil-pbc-proetale-constant-exact);
restriction along `π_{T',n}` is exact.
Step 3: for exact functors the universal left-derived counit is termwise localization
(lem-weil-pbc-exact-functor-derived-functor), invertible on every complex; this gives the
evaluation factor and `δ`.
Step 4: `u_{n,P}` is the exact evaluation factor after `ε^V_{R⁰P} ∘ V_g(ε^R_P)`; the
three naturality squares compose, so `u_n` is natural.
Step 5: for K-flat `P`, `R⁰_T` preserves quasi-isomorphisms between K-flat complexes
(lem-pur-derived-change-of-rings (1), levelwise cohomology) and cones; with
lem-pc-kflat-resolution and lem-pur-left-derived-from-kflat-class the counit `ε^R_P` is
invertible, hence so is `u_{n,P}`.
Step 6: the scalar-extension counit is invertible on K-flat `P`
(lem-pur-derived-change-of-rings), so `v_{n,P}` and `b_{n,P} = δ Res(v)` are invertible.
Step 7: on K-flat `P` put `a_P = b_{n,P}⁻¹ Q(E_n(P)) u_{n,P}`; it is natural in `P`
up to homotopy.
Step 8: quasi-isomorphisms have a calculus of fractions
(lem-pur-quasi-isos-saturated-triangulated); every complex has a K-flat resolution;
lem-sc-nattrans-from-resolving-class extends `a` and
lem-weil-pbc-localization-universal-property descends it to `e_n`.
Step 9: `e_n(QX) = J_n(Qs) a_P U_n(Qs)⁻¹` for a K-flat resolution `s : P → X`, so `e_n`
is invertible; any normalized `e'_n` agrees with `a_P` on K-flat `P`, hence with `e_n`.
The selected `completedReductionFiniteEvaluation` therefore satisfies the normalization. -/
theorem completedReductionFiniteEvaluation_normalized (n : ℕ) :
    (completedCoefficientMap g d = (d.integralRingIso g).hom ∧
      IsIso (completedCoefficientMap g d)) ∧
    (PreservesFiniteLimits (completedModulePullback g d) ∧
      PreservesFiniteColimits (completedModulePullback g d) ∧
      PreservesFiniteLimits (completedTowerModulePullback g d) ∧
      PreservesFiniteColimits (completedTowerModulePullback g d)) ∧
    (∀ {P P' : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ} (h : P ⟶ P'),
      (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map
          ((completedTowerPullback g d).map
            ((completedReductionTower Y d).map (DerivedCategory.Q.map h))) ≫
        completedReductionPulledModelMap g d n P' =
      completedReductionPulledModelMap g d n P ≫
        DerivedCategory.Q.map
          ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
            (op n)).mapHomologicalComplex (.up ℤ)).map
              (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).map
                (((completedReductionModuleTowerFunctor Y d).mapHomologicalComplex
                  (.up ℤ)).map h)))) ∧
    (∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
        IsIso (completedReductionPulledModelMap g d n P) ∧
          IsIso (completedReductionFiniteModelMap g d n P)) ∧
    (∃! e : completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n),
      HasCompletedReductionFiniteEvaluationNormalization g d n e) ∧
    HasCompletedReductionFiniteEvaluationNormalization g d n
      (completedReductionFiniteEvaluation g d n) := by
  let := completedReductionModuleTowerFunctor_additive Y d
  let := completedTowerModulePullback_additive g d
  have hc := completedCoefficientMap_eq_integralRingIso g d
  refine ⟨⟨hc, ?_⟩,
    ⟨completedReductionPullback_preservesFiniteLimits g d,
      completedReductionPullback_preservesFiniteColimits g d,
      completedReductionTowerPullback_preservesFiniteLimits g d,
      completedReductionTowerPullback_preservesFiniteColimits g d⟩,
    ?_, ?_, completedReductionFiniteEvaluation_exists g d n, ?_⟩
  · rw [hc]
    infer_instance
  · intro P P' h
    exact (completedReductionPulledModelNat g d n).naturality h
  · intro P hP
    exact ⟨completedReductionPulledModelNat_isIso g d n P hP,
      completedReductionFiniteModelMap_isIso g d n P hP⟩
  · exact (completedReductionFiniteEvaluation_exists g d n).exists.choose_spec

end AlgebraicGeometry.Scheme
