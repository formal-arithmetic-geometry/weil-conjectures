/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Etale scalar extension of inertia and invariant squares

Source: Stacks Project, `pione.tex`, Tags 0BSS (`lemma-inertia-base-change`) and
0BST (`lemma-inertia-invariants-etale`), first two reduction paragraphs.
(blueprint: lem-dl-a1-etale-base-change-inertia-square)

The fixed-point families use the existing `AlgHom.fixedPoints` construction.
The localized tensor product is identified with the literal localization by an
isomorphism whose value on every element of the original tensor product is specified.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

variable (G : Type v) [Group G] (R : Type u) [CommRing R] [MulSemiringAction G R]

/-- The given action, viewed over its full fixed ring.
Source: Stacks Project, Tag 0BST, second reduction paragraph.
(blueprint: lem-dl-a1-etale-base-change-inertia-square) -/
def inertiaSquareAction : G → R →ₐ[FixedPoints.subring R G] R :=
  MulSemiringAction.toAlgHom (FixedPoints.subring R G) R

/-- Restriction of the same action to the inertia subgroup, without changing its base ring.
Source: Stacks Project, Tags 0BSS and 0BST.
(blueprint: lem-dl-a1-etale-base-change-inertia-square) -/
def inertiaSquareRestrictedAction (q : Ideal R) :
    q.inertia G → R →ₐ[FixedPoints.subring R G] R :=
  fun g ↦ inertiaSquareAction G R g.val

variable (B : Type u) [CommRing B] [Algebra (FixedPoints.subring R G) B]

/-- Scalar extension of the inclusion of inertia invariants, written using a comparison
isomorphism normalized on pure tensors in `InertiaSquareAssertions` below.
Source: Stacks Project, Tag 0BST, displayed square in the second reduction paragraph.
(blueprint: lem-dl-a1-etale-base-change-inertia-square) -/
noncomputable def inertiaSquareRightMap (q : Ideal R)
    (e : B ⊗[FixedPoints.subring R G] AlgHom.fixedPoints (inertiaSquareRestrictedAction G R q)
      ≃ₐ[B] AlgHom.fixedPoints
        (AlgHom.baseChangeFamily B (inertiaSquareRestrictedAction G R q))) :
    AlgHom.fixedPoints (inertiaSquareRestrictedAction G R q) →+*
      AlgHom.fixedPoints (AlgHom.baseChangeFamily B (inertiaSquareRestrictedAction G R q)) :=
  e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

/-- The inertia, invariant-ring, cartesian-square and contracted-point assertions for
one scalar extension. Inertia is expressed by its standard difference criterion:
`g(t) - t ∈ Q` for every `t`. For a finite group this is exactly preservation of `Q`
and the identity on `Frac(S / Q)` (as in `Ideal.inertia`). The two fixed-point
algebras are the existing upstream construction, not additional invariant-ring data.
Source: Stacks Project, Tags 0BSS and 0BST, first two reduction paragraphs.
(blueprint: lem-dl-a1-etale-base-change-inertia-square) -/
def InertiaSquareAssertions (q : Ideal R)
    (Q : Ideal (B ⊗[FixedPoints.subring R G] R)) : Prop :=
  (∀ g : G,
    (∀ s : B ⊗[FixedPoints.subring R G] R,
      AlgHom.baseChangeFamily B (inertiaSquareAction G R) g s - s ∈ Q) ↔ g ∈ q.inertia G) ∧
  ∃ (_ : B ≃ₐ[B] AlgHom.fixedPoints (AlgHom.baseChangeFamily B (inertiaSquareAction G R)))
    (e : B ⊗[FixedPoints.subring R G] AlgHom.fixedPoints (inertiaSquareRestrictedAction G R q)
      ≃ₐ[B] AlgHom.fixedPoints
        (AlgHom.baseChangeFamily B (inertiaSquareRestrictedAction G R q))),
    (∀ (b : B) (x : AlgHom.fixedPoints (inertiaSquareRestrictedAction G R q)),
      (e (b ⊗ₜ x) : B ⊗[FixedPoints.subring R G] R) = b ⊗ₜ (x : R)) ∧
    IsPullback
      (Spec.map (CommRingCat.ofHom (inertiaSquareRightMap G R B q e)))
      (Spec.map (CommRingCat.ofHom (algebraMap B _)))
      (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subring R G)
        (AlgHom.fixedPoints (inertiaSquareRestrictedAction G R q)))))
      (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subring R G) B))) ∧
    Etale (Spec.map (CommRingCat.ofHom (inertiaSquareRightMap G R B q e))) ∧
    Etale (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subring R G) B))) ∧
    Ideal.comap (inertiaSquareRightMap G R B q e)
      (Ideal.comap (AlgHom.fixedPoints
        (AlgHom.baseChangeFamily B (inertiaSquareRestrictedAction G R q))).val.toRingHom Q) =
      Ideal.comap (AlgHom.fixedPoints (inertiaSquareRestrictedAction G R q)).val.toRingHom q

/-- The canonical map on tensor products induced by `B → B[1/b]`.
Source: Stacks Project, Tag 0BST, etale-localization reduction, with the fraction
calculation in the proof of the node.
(blueprint: lem-dl-a1-etale-base-change-inertia-square) -/
noncomputable def inertiaSquareLocalizationMap (b : B) :
    B ⊗[FixedPoints.subring R G] R →+*
      Localization.Away b ⊗[FixedPoints.subring R G] R :=
  (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom (FixedPoints.subring R G) B (Localization.Away b))
    (AlgHom.id (FixedPoints.subring R G) R)).toRingHom

/-- Etale scalar extension preserves inertia and the invariant square, also after every
principal localization avoiding the chosen prime. The local tensor ring is explicitly
identified with `S[1/b]`, and its prime is the extension of `Q` under the canonical map.
No assumption of module-finiteness, faithful action or invertibility of the group order
is made.

Source: Stacks Project, Tags 0BSS and 0BST, first two reduction paragraphs.
(blueprint: lem-dl-a1-etale-base-change-inertia-square)

Proof:
1. Use the difference criterion for inertia. Contraction tests it on `1 tensor r`;
   conversely tensor generation expresses each difference as a sum of multiples of
   `1 tensor (g(r)-r)`. This proves the equality without flatness.
2. By lem-weil-pbc-etale-algebra-flat, B is flat. Apply
   lem-dl-a1-flat-base-change-finite-invariants (`AlgHom.tensorFixedPointsEquiv`)
   to G and to I. The first source identifies with B; the second comparison is
   normalized on pure tensors by `AlgHom.coe_tensorFixedPointsEquiv_tmul`.
3. Apply lem-weil-pbc-fibre-product-affine-spectra (`pullbackSpecIso`) with its
   specified projections. The normalization identifies the arrows with the canonical
   inclusions and gives the asserted cartesian square.
4. The bottom arrow is etale by hypothesis; the top is its base change, by
   lem-weil-pbc-etale-scheme-base-change.
5. An invariant x maps into Q exactly when x belongs to q, by contraction. This
   proves the identity of contracted ideals, hence the asserted image of the point.
6. For b avoiding Q, lem-weil-pbc-etale-algebra-finite-presentation-localization
   makes B[1/b] etale. The canonical fraction map identifies B[1/b] tensor R with
   S[1/b] and is G-equivariant. The extended ideal is prime since its quotient is
   (S/Q)[1/b], a nonzero domain, and contracts to Q and then q. Repeat steps 1--5.
   Only flatness and finite-group invariants were used, never module-finiteness or
   division by the group order.
-/
theorem etale_baseChange_inertia_square [Finite G]
    [Algebra.Etale (FixedPoints.subring R G) B]
    (q : Ideal R) [q.IsPrime]
    (Q : Ideal (B ⊗[FixedPoints.subring R G] R)) [Q.IsPrime]
    (hQ : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom Q = q) :
    InertiaSquareAssertions G R B q Q ∧
    ∀ b : B, algebraMap B (B ⊗[FixedPoints.subring R G] R) b ∉ Q →
      (∃ e : Localization.Away (algebraMap B (B ⊗[FixedPoints.subring R G] R) b)
          ≃+* (Localization.Away b ⊗[FixedPoints.subring R G] R),
        ∀ s : B ⊗[FixedPoints.subring R G] R,
          e (algebraMap _ _ s) = inertiaSquareLocalizationMap G R B b s) ∧
      (Ideal.map (inertiaSquareLocalizationMap G R B b) Q).IsPrime ∧
      Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
        (Ideal.map (inertiaSquareLocalizationMap G R B b) Q) = q ∧
      InertiaSquareAssertions G R (Localization.Away b) q
        (Ideal.map (inertiaSquareLocalizationMap G R B b) Q) := by
  sorry

end AlgebraicGeometry
