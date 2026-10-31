/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# The directed union of finite étale subalgebras

Source: Stacks Project, Tags 0CKR, 0CKS and 0CKT, the finite-stage union construction
(blueprint: lem-sfb-finite-etale-subalgebra-directed-union).

The algebraic predicates below are exactly finiteness and étaleness of the affine
structure morphism, by `AlgebraicGeometry.IsFinite.SpecMap_iff`,
`AlgebraicGeometry.HasRingHomProperty.Spec_iff`, and `RingHom.etale_algebraMap`.
-/

@[expose] public section

universe u v w

namespace Algebra

/-- The family of unital finite étale subalgebras of a field algebra, including the
zero algebra. Source: Stacks Project, Tags 0CKR and 0CKS
(blueprint: lem-sfb-finite-etale-subalgebra-directed-union). -/
def finiteEtaleSubalgebras (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] : Set (Subalgebra k A) :=
  {D | Module.Finite k D ∧ Etale k D}

/-- The canonical supremum of the finite étale subalgebras. Its underlying set is
their set-theoretic union by `finiteEtaleSubalgebra_directed_union` below.
Source: Stacks Project, Tag 0CKS
(blueprint: lem-sfb-finite-etale-subalgebra-directed-union). -/
def finiteEtaleSubalgebraUnion (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] : Subalgebra k A :=
  sSup (finiteEtaleSubalgebras k A)

/-- Finite étale subalgebras form a nonempty directed family; their union is a
subalgebra containing every idempotent, finite subsets lie in one stage, and maps
from finite étale algebras have finite étale image and factor uniquely through it.
Source: Stacks Project, Tags 0CKR, 0CKS and 0CKT
(blueprint: lem-sfb-finite-etale-subalgebra-directed-union).

Proof plan:
1. By `lem-weil-pbc-etale-algebra-over-field-product`, a finite étale algebra is a
finite product of finite separable field extensions. Every ideal in such a product
is cut out by coordinate idempotents: if a kernel element has a nonzero coordinate,
multiplication by its coordinate inverse puts that coordinate idempotent in the
kernel. Thus the image of any algebra map is the product of the surviving factors.
It is finite étale by `lem-weil-pbc-finite-separable-extension-etale`,
`lem-weil-pbc-etale-algebra-finite-product`, and the finite-module criterion in
`def-weil-finite-integral-morphism`. The empty surviving product is allowed.
2. Apply this image assertion to the structure map from k. This gives a member
of the family even when A is zero.
3. Given D and E, multiplication maps D tensor E into A. The tensor product is
étale by `lem-weil-pbc-etale-ring-base-change` and clause (2) of
`lem-weil-pbc-etale-composition-cancellation`. Tensors of finite spanning families
span it, so it is finite. Its image is a finite étale subalgebra containing D and E.
4. Directedness and nonemptiness show that the set-theoretic union is closed under
addition, multiplication, negation and scalars, hence equals the subalgebra supremum.
5. Induction on the size of a finite subset, using a common upper bound at each
successor step, puts it in one member; the empty subset uses nonemptiness.
6. For e squared equal to e, the map k times k to A given by (a,b) mapping to
 a e + b (1-e) is a unital algebra map with e in its image. The image assertion
puts e in the union. Any map from a finite étale algebra has image in the union,
so corestricts to it; injectivity of the inclusion gives uniqueness.
-/
theorem finiteEtaleSubalgebra_directed_union (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] :
    (finiteEtaleSubalgebras k A).Nonempty ∧
    DirectedOn (· ≤ ·) (finiteEtaleSubalgebras k A) ∧
    (finiteEtaleSubalgebraUnion k A : Set A) =
      (⋃ D ∈ finiteEtaleSubalgebras k A, (D : Set A)) ∧
    (∀ s : Set A, s.Finite → s ⊆ (finiteEtaleSubalgebraUnion k A : Set A) →
      ∃ D ∈ finiteEtaleSubalgebras k A, s ⊆ (D : Set A)) ∧
    (∀ e : A, e ^ 2 = e → e ∈ finiteEtaleSubalgebraUnion k A) ∧
    (∀ (C : Type w) [CommRing C] [Algebra k C], Module.Finite k C → Etale k C →
      ∀ h : C →ₐ[k] A, h.range ∈ finiteEtaleSubalgebras k A ∧
        ∃! g : C →ₐ[k] finiteEtaleSubalgebraUnion k A,
          (finiteEtaleSubalgebraUnion k A).val.comp g = h) := by
  sorry

end Algebra
