/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIntegralClosure

/-!
# Universal integral factorization of an algebraic-space morphism

Source: Stacks Project, Morphisms of Spaces, Tags 0822 and 0823, restricted to separated
morphisms (blueprint: lem-sfb-space-relative-integral-factorization).

Quasi-compactness is written on all quasi-compact scheme tests, exactly as in the node.
Integrality and the closed diagonal use the existing scheme-test representability predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every quasi-compact separated morphism of algebraic spaces has an initial integral
factorization. Both triangles are part of the unique mediator's defining property.
Source: Stacks Project, Morphisms of Spaces, Tags 0822 (definition-normalization-X-in-Y)
and 0823 (lemma-characterize-normalization), the separated specialization
(blueprint: lem-sfb-space-relative-integral-factorization).

Proof:
1. For any g : Z → X and quasi-coherent algebra D, the fibre-product universal property
   identifies maps Z → Spec_X D over X with sections after base change to Z.
   By lem-sfb-space-relative-spec-correspondence, those sections are algebra maps
   g^*D → O_Z. The tensor/direct-image adjunction of def-trf-space-etale-module-functors
   identifies these with algebra maps D → g_*O_Z: on tensors the transpose sends
   b tensor d to b times the image of d. These inverse correspondences respect composition.
2. Put A = f_*O_Y. The unit module O_Y is quasi-coherent, so A is quasi-coherent by
   lem-trf-space-qc-separated-quasi-coherent-pushforward: the hypothesis supplies every
   affine scheme test in that theorem, and the closed diagonal is its separatedness.
   By lem-sfb-space-quasicoherent-integral-closure, take its quasi-coherent integral
   closure B of O_X. Set N = Spec_X B. The integral-algebra test in the relative-Spec
   correspondence makes n : N → X integral on every scheme test. The inclusion B → A
   corresponds by step 1 to i : Y → N over X, giving i ≫ n = f.
3. For q : T → X integral and a : Y → T over X, integrality implies affineness.
   The relative-Spec correspondence identifies T with Spec_X C for C = q_*O_T.
   Step 1 turns a into an algebra map chi : C → A. On an affine etale chart, every
   element of C satisfies a monic equation over O_X, and applying chi preserves that
   equation. Thus chi factors through B. The factors commute with restrictions since
   their composites with the inclusion into A agree; they glue to an algebra map
   C → B. Contravariance supplies h : N → T over X, giving h ≫ q = n. Composition
   in step 1 identifies i ≫ h with a, since the algebra map composed with B → A is chi.
4. Any other h' satisfying both triangles gives an algebra map C → B whose composite
   with B → A is also chi. The inclusion is componentwise injective, so the algebra
   maps coincide. Faithfulness of the relative-Spec correspondence gives h' = h.
   No representability or finiteness assumption is placed on a. -/
theorem exists_relative_integral_factorization {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (hqc : ∀ (T : Over S), CompactSpace T.left →
      ∀ t : yoneda.obj T ⟶ X.obj.obj,
        ∃ (U : Over S) (a : yoneda.obj U ⟶ Limits.pullback f.hom.hom t),
          CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (Limits.pullback.diagonal f.hom.hom)) :
    ∃ (N : AlgebraicSpace S) (i : Y ⟶ N) (n : N ⟶ X),
      i ≫ n = f ∧
      IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) n.hom.hom ∧
      ∀ (T : AlgebraicSpace S) (q : T ⟶ X),
        IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) q.hom.hom →
        ∀ a : Y ⟶ T, a ≫ q = f →
          ∃! h : N ⟶ T, i ≫ h = a ∧ h ≫ q = n := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
