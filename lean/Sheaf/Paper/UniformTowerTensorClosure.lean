/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.SmoothPurityTowerGamma

/-! # Tensor closure of ordinary uniformly constructible finite-Tor towers

Source: blueprint smooth-purity base-change factors, proof (2), tensor domains;
blueprint lem-sf-tensor-ctf (i),(ii), applied levelwise.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.UniformTowerTensorClosure

/-- Ordinary tensor preserves the uniform constructible finite-Tor domain, without
any normalization assumption on either tower.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md, proof (2), domains;
lem-sf-tensor-ctf (i),(ii).
(blueprint: lem-sp-uniform-tower-tensor-closure).

Proof: choose common cohomological and Tor intervals for K and L. Exact evaluation,
the realization counit, and tensorEvaluation identify each level of the displayed
object with the ordinary derived tensor of the two corresponding finite levels.
For each finite constant coefficient ring, descend the two bounded constructible
complexes to the etale site. Reflect their specified Tor intervals through finite
coefficient comparison. The bounded constructible tensor theorem proves
constructibility, and the Tor tensor theorem adds the two Tor intervals. The
comparison tensor isomorphism carries both conclusions back to the intrinsic
pro-etale tensor. Testing its Tor interval against the coefficient unit also gives
cohomology in that same sum interval. All four endpoints are independent of the
level, so these conclusions supply the required common intervals. Transport along
the evaluation isomorphisms. This uses no transition map being invertible and
includes zero towers, empty schemes, the first positive level, coincident interval
endpoints, and ramified coefficient extensions. -/
theorem tensor_mem
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (b : SpTowerShriek.Base ell E) (q : SpTowerCalculus.Coordinates ell E b)
    (T : Scheme.{u}) [IsNoetherian T]
    (K L : spDerivedCoefficientTowers ell E T (q.abelian T))
    (hK : spConstructibleTorTowers ell E T (q.abelian T) K)
    (hL : spConstructibleTorTowers ell E T (q.abelian T) L) :
    spConstructibleTorTowers ell E T (q.abelian T)
      ((SpTowerCalculus.realization ell E b T (q.abelian T)).inverse.obj
        ((SpTowerShriek.tensor ell E b T).obj
          ((SpTowerCalculus.realization ell E b T (q.abelian T)).functor.obj K,
            (SpTowerCalculus.realization ell E b T (q.abelian T)).functor.obj L))) := by
  sorry

end AlgebraicGeometry.ProEtale.UniformTowerTensorClosure
