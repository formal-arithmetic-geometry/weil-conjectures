/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Injective homomorphisms of algebraic groups are closed immersions

Source: Milne, Algebraic Groups (2017), Proposition 5.31(a) and Theorem 5.34,
printed pp.106--107, first proof through Theorem 5.28
(blueprint: lem-sfb-algebraic-group-monomorphism-closed-immersion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An injective homomorphism of separated finite-type group schemes over a field
is a closed immersion. Injectivity is required on points over every commutative
algebra, including nonreduced algebras, rather than only over field extensions.

Source: Milne, Algebraic Groups (2017), Proposition 5.31(a),(b) and Theorem 5.34,
printed pp.106--107, first proof through Theorem 5.28
(blueprint: lem-sfb-algebraic-group-monomorphism-closed-immersion).

Proof plan:
1. Extend injectivity from affine test schemes to every k-scheme by restricting
   to an affine open cover and gluing equality. The kernel fibre product
   (def-sc-group-scheme, def-pc-fibre-product) then has only the identity point
   on every test scheme. Its structure map and identity section are inverse,
   by testing on the kernel itself; hence the scheme-theoretic kernel is trivial.
2. Apply lem-sfb-trivial-kernel-homogeneous-quotient to u, obtaining a finite-type
   scheme X, a B-action, a distinguished point o and its orbit map q. The coset
   criterion with the identity says q(b)=o exactly when b belongs to the image
   of u, for points over every test scheme. In particular q u=o pi_A.
3. The square formed by u, q, o and pi_A is cartesian: its compatible test
   points lift by step 2 and lift uniquely by step 1. Use the universal property
   of def-pc-fibre-product to identify A with that fibre product.
4. The map o:Spec k to X is a closed immersion by the affine criterion
   (def-weil-affine-spectrum, def-weil-closed-immersion; Stacks Tag 01QO).
   The preimage of an affine open Spec C is empty or all of Spec k. In the
   latter case C to k is surjective since it fixes constants; in the former,
   use the quotient C/C=0. Apply lem-weil-pbc-closed-immersion-base-change
   (Stacks Tag 01QR) along q. Step 3 identifies its closed projection with u. -/
theorem isClosedImmersion_of_injective_algebraPoints
    {k : Type u} [Field k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
    [IsSeparated A.hom] [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    (u : A ⟶ B) [IsMonHom u]
    (hinj : ∀ (R : Type u) [CommRing R] [Algebra k R],
      Function.Injective
        (fun x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ A => x ≫ u)) :
    IsClosedImmersion u.left := by
  sorry

end AlgebraicGeometry
