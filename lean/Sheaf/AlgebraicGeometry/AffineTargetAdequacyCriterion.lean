/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Global power lifting over an affine target

Source: Alper, *Adequate moduli spaces and geometrically reductive group schemes*,
arXiv:1005.2398v3, Remark 4.1.3 and Lemma 4.1.8(2),(3), printed pp. 17--20
(blueprint: lem-sfb-affine-target-adequacy-criterion).

The affine target is its representable fibred groupoid over Spec k. The proof of its
algebraicity required by the existing adequate-affineness predicate is existentially
bound in the conclusion, so it is not an additional hypothesis. Global sections and
quasi-coherent algebras are those of the existing big fppf site.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry Opposite

namespace CategoryTheory

/-- Over an affine target, adequate affineness is equivalent to positive-power
lifting on global sections for every surjection of arbitrary quasi-coherent algebras.
Source: Alper, arXiv:1005.2398v3, Remark 4.1.3 and Lemma 4.1.8(2),(3)
(blueprint: lem-sfb-affine-target-adequacy-criterion).

Proof:
1. Assume adequate affineness and apply its smooth-test condition to the identity
   of Spec A. Refine the resulting etale covering to a finite affine family using
   lem-weil-pbc-etale-covering-sieve-finite-affine-refinement. The test stacks are
   algebraic by lem-sfb-algebraic-stack-fibre-products.
2. For the empty target use exponent one and zero. Otherwise multiply the positive
   local exponents and take the product S of the chart rings. The nodes
   lem-weil-pbc-finite-affine-coproduct-spectrum, lem-weil-pbc-etale-algebra-flat,
   lem-weil-pbc-finite-product-flat-modules and
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat show A -> S faithfully flat.
   Raise each local lift to the common exponent and glue on the disjoint components.
3. Apply lem-sfb-stack-flat-scalar-sections to identify the lift over S with a
   tensor-extended global section. Form the cokernel of the global-section map.
   By lem-weil-pbc-tensor-right-exact its target class vanishes after tensoring with S;
   lem-weil-pbc-faithfully-flat-universally-injective makes it vanish before tensoring,
   producing the global lift.
4. Conversely, on an affine open V of any smooth test, its base-change projection
   to U is affine. By lem-sfb-stack-affine-algebra-direct-image, pushforward takes
   algebra surjections on U_V to surjections on U and identifies their section rings
   naturally. Apply the assumed global power lifting and transfer the lift back.
5. Restriction to U_V is precomposition as in def-sfb-stack-quasi-coherent-algebra;
   it preserves local surjectivity and local free presentations. Apply step 4 to the
   restricted original surjection. The affine opens cover the smooth test etale-locally,
   giving universal adequacy. Together with the given qcqs assumptions this is
   def-sfb-adequately-affine-morphism. The representable target is an algebraic stack:
   its diagonal is representable and its identity scheme atlas is smooth surjective.
-/
theorem adequatelyAffine_iff_global_power_lifting
    {k : Type u} [Field k] (A : Type u) [CommRing A] [Algebra k A]
    (U : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hU : IsAlgebraicModuliStack U)
    (f : BasedFunctor U
      (discreteModuli (yoneda.obj
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))))))
    (_hqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} f)
    (_hqs : IsQuasiSeparatedAlgebraicModuliMap f) :
    (∃ hY : IsAlgebraicModuliStack
        (discreteModuli (yoneda.obj
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))))),
      IsAdequatelyAffineMorphism f hU hY) ↔
      ∀ (B C : ModuliAlgebraSheaf U hU.1.1) (q : B ⟶ C),
        IsQuasicoherentModuliAlgebra B → IsQuasicoherentModuliAlgebra C →
        IsSurjectiveModuliAlgebra q → ∀ t : moduliGlobalSectionsRing C.right,
          ∃ N : ℕ, 0 < N ∧ ∃ s : moduliGlobalSectionsRing B.right,
            ∀ x : U.objᵒᵖ, (q.right.hom.app x) (s.1 x) = (t.1 x) ^ N := by
  sorry

end CategoryTheory
