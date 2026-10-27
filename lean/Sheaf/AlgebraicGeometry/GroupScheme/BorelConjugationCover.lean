/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
import Sheaf.AlgebraicGeometry.TorusRegularSemisimpleElement
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Conjugates of a Borel subgroup cover a connected affine algebraic group

Source: Milne, Algebraic Groups (2017), Definition 17.6 and the following sentence,
printed pp.353–354; Theorem 17.33(b) and Corollary 17.34, printed p.362.
(blueprint: lem-sfb-borel-conjugation-cover)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Borel subgroups exist, and conjugation from any prescribed Borel is surjective
on rational points. Solvability in `IsBorelGroupScheme` is termination of the
scheme-theoretic derived series. Rational points are morphisms from the unit
object, the base field's spectrum. No reductivity hypothesis is needed.

Source: Milne, Definition 17.6 and the following sentence, printed pp.353–354;
Theorem 17.33(b), its proof, and Corollary 17.34, printed p.362.
(blueprint: lem-sfb-borel-conjugation-cover)

Proof, following the six steps of the node:
1. Start with the trivial smooth connected solvable subgroup and choose one of largest
   dimension. The dimension bounds and strict dimension increase for proper smooth
   connected inclusions in lem-sfb-solvable-normal-subgroup-products make it maximal.
   The same argument extends any smooth connected solvable subgroup to a Borel.
2. For the prescribed Borel B, choose a maximal torus T inside B using
   lem-sfb-borel-maximal-torus-conjugacy. By
   lem-sfb-neutral-torus-centralizer-cartan-structure, C = C_G(T)⁰ is smooth connected
   solvable, contains T, and has the stated product structure and finite normalizer quotient.
3. Extend C to a Borel B′. By lem-sfb-torus-normalizer-borel-transitivity, an element
   normalizing T conjugates B′ to B. It preserves C, so C is contained in B.
4. Choose the regular semisimple t of lem-sfb-torus-regular-semisimple-element and form
   G/C by lem-sfb-homogeneous-orbit-quotient-geometry. If t fixes xC, then x⁻¹tx lies in C
   and is semisimple, hence lies in T. Therefore xTx⁻¹ centralizes t and lies in C_G(T).
   Its connectedness puts it in C, using lem-sfb-group-neutral-component-translates.
   Every torus in C lies in T, so maximality implies xTx⁻¹ = T. Thus x normalizes C.
   The fixed cosets inject into the finite quotient of its rational normalizer by C(k).
5. Apply the finite-fixed-coset clause of lem-sfb-subgroup-conjugation-incidence-criterion
   to C and t. A nonempty open V has rational points in the conjugates of C, hence of B.
6. Form G/B using lem-sfb-homogeneous-orbit-quotient-geometry. By
   lem-sfb-borel-quotient-proper-geometry, G/B is proper and G is integral. The proper
   quotient clause of lem-sfb-subgroup-conjugation-incidence-criterion makes the
   conjugation saturation of B the rational points of a closed subset Z. If Z is proper,
   irreducibility makes V meet its open complement. By lem-sc-lft-over-field-jacobson-space
   this intersection has a closed point, and lem-weil-pbc-closed-point-residue-field-base
   makes it rational. This contradicts V(k) being in Z(k). Thus Z is all of G, giving
   exactly the displayed surjectivity. -/
theorem exists_borelGroupScheme_and_conjugation_surjective
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left] :
    (∃ (B : Over (Spec (.of k))) (_ : GrpObj B) (i : B ⟶ G), IsBorelGroupScheme i) ∧
      (∀ (B : Over (Spec (.of k))) [GrpObj B] (i : B ⟶ G), IsBorelGroupScheme i →
        Function.Surjective
          (fun p : (𝟙_ (Over (Spec (.of k))) ⟶ G) ×
              (𝟙_ (Over (Spec (.of k))) ⟶ B) ↦
            p.1 * (p.2 ≫ i) * p.1⁻¹)) := by
  sorry

end AlgebraicGeometry
