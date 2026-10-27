/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.ProEtaleOrderedIntegration

/-! # Site comparison of a normalized affine-line counit

Source: blueprint sk-prop-an, affine-space top trace, proof paragraphs 1--2;
Stacks 099R, 09AF, 0B65, and 0GL1.
(blueprint: lem-pur-line-counit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- Canonical site comparison preserves the independently normalized line counit
on every bounded-below ordinary coefficient. Source: blueprint affine-space top trace,
proof paragraphs 1--2; Stacks 099R, 09AF, 0B65, and 0GL1
(blueprint: lem-pur-line-counit-comparison).

Proof: CartierKummerChern identifies the supported pro-etale Chern arrow with the
ordinary Chern arrow under the root-normalized Tate comparison. The inverse-image
comparison and direct-image counit mate identify their adjoints and the twisted
unit components. The biproduct injections identify the projective decompositions;
inverting and taking the second projection identifies their traces. The proper
projection comparison, including symmetry, tensor comparison, and right unitor,
therefore carries the ordinary coefficient counit to projectiveEpsilon, by its
unique ProperIntegrationEquation. The exact open-extension comparison preserves
the open counit: transpose the two expressions under the open adjunction, where
both are the identity with the same inverse-image comparison. Compose the proper
and open equations and use naturality of the direct-image mate. The resulting
source comparison is exactly lineSiteComparison, which is defined from that mate
and extension comparison. This yields the displayed equality. All arguments work
for every Noetherian base with l invertible, with no finite-type field hypothesis,
and for the zero coefficient ring and empty scheme.
-/
theorem lineCounit_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    lineCounit l E n T hT (infinityCartier T) r hA K =
      (lineSiteComparison (Scheme.finiteTateCoefficient l E n) T
        ⟨_, rightTower_plus l E n T hT r hA 1 K⟩).hom ≫
      (comparison (Scheme.finiteTateCoefficient l E n) T).map
        ((Etale.affineTraceLineAdjunction _ (l ^ (r + 1)) hA
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          T (by simpa only [Nat.cast_pow] using hT.pow (r + 1))
          (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA
            T (by simpa only [Nat.cast_pow] using hT.pow (r + 1)))).counit.app K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
