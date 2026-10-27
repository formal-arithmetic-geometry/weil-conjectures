/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Invariant.Basic

/-!
# Invariants of a transitive product of domains

Source: the coordinate calculation for the finite constant action groupoid accompanying
Stacks Project, Tag 03BK, `lemma-invariants-base-change`, part (3), and Mathlib's
`IsFractionRing.isInvariant` (blueprint: lem-sfb-transitive-domain-product-invariants).
The equalizer intersections below spell out fixed rings using the coordinate isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v w a k l

namespace RingTheory

/-- The fixed subring of the product: its elements satisfy `(h b) (h i) = ρ h i (b i)`
and `h b = b`, expressed without choosing a separate action instance on the product.
Source: coordinate calculation accompanying Stacks Tag 03BK, part (3)
(blueprint: lem-sfb-transitive-domain-product-invariants). -/
def transitiveProductFixedSubring
    {H : Type u} [Group H] {I : Type v} [MulAction H I]
    (B : I → Type w) [∀ i : I, CommRing (B i)]
    (ρ : ∀ (h : H) (i : I), B i ≃+* B (h • i)) : Subring (∀ i : I, B i) :=
  ⨅ (h : H) (i : I),
    (Pi.evalRingHom B (h • i)).eqLocus ((ρ h i).toRingHom.comp (Pi.evalRingHom B i))

/-- The fixed subring of a chosen factor under its stabilizer. The cast merely identifies
`B (h • i)` with `B i` using the stabilizer equality, and imposes no normality condition.
Source: coordinate calculation accompanying Stacks Tag 03BK, part (3)
(blueprint: lem-sfb-transitive-domain-product-invariants). -/
def transitiveStabilizerFixedSubring
    {H : Type u} [Group H] {I : Type v} [MulAction H I]
    (B : I → Type w) [∀ i : I, CommRing (B i)]
    (ρ : ∀ (h : H) (i : I), B i ≃+* B (h • i)) (i : I) : Subring (B i) :=
  ⨅ (h : H) (hi : h • i = i),
    ((ρ h i).trans (RingEquiv.cast (R := B) hi)).toRingHom.eqLocus (RingHom.id (B i))

/-- Projection identifies product invariants with stabilizer invariants; a ring mapping
injectively onto the product invariants is a domain and has the stated invariant fraction field.
Source: the coordinate calculation accompanying Stacks Tag 03BK, part (3), together with
Mathlib `IsFractionRing.isInvariant`
(blueprint: lem-sfb-transitive-domain-product-invariants).

Proof plan: (1) Construct the product action by transporting coordinates with `ρ`.
The identity and cocycle laws give its action laws, and it carries each coordinate
idempotent to that of the translated index. The uniqueness in
`lem-sfb-domain-product-action-fixed-ring` identifies its factor maps with `ρ`.
(2) Transitivity permits the singleton representative set `{i}` in that node;
its projection isomorphism gives the first assertion.
(3) Corestrict `u` to the fixed ring and compose with this isomorphism. Its projection
is injective and has precisely the stabilizer-fixed image. Pull back nontriviality and
absence of zero divisors from `B i` to obtain `IsDomain A`.
(4) Use `lem-weil-pbc-fraction-field-lift` to extend the projected injection uniquely
and to extend the stabilizer automorphisms; on quotients these are the displayed
numerator/denominator action. Uniqueness supplies the action laws.
(5) Apply `lem-sfb-finite-invariant-fraction-field-lifting` to the finite stabilizer
and the projected injection to obtain that every fixed fraction is in the image.
Conversely, the numerator and denominator of each image fraction are stabilizer-fixed,
so its image is fixed. No step divides by the group order. -/
theorem transitive_domain_product_invariants
    (H : Type u) [Group H] [Finite H]
    (I : Type v) [Finite I] [Nonempty I] [MulAction H I]
    (htrans : ∀ i j : I, ∃ h : H, h • i = j)
    (B : I → Type w) [∀ i : I, CommRing (B i)] [∀ i : I, IsDomain (B i)]
    (ρ : ∀ (h : H) (i : I), B i ≃+* B (h • i))
    (hρone : ∀ i : I,
      (ρ 1 i).trans (RingEquiv.cast (R := B) (one_smul H i)) = RingEquiv.refl (B i))
    (hρmul : ∀ (g h : H) (i : I),
      (ρ (g * h) i).trans (RingEquiv.cast (R := B) (mul_smul g h i)) =
        (ρ h i).trans (ρ g (h • i))) (i : I) :
    (∃ e : transitiveProductFixedSubring B ρ ≃+* transitiveStabilizerFixedSubring B ρ i,
      ∀ b : transitiveProductFixedSubring B ρ, (e b : B i) = (b : ∀ j : I, B j) i) ∧
    (∀ (A : Type a) [CommRing A] (f : A →+* (∀ j : I, B j)),
      Function.Injective f →
      f.range = transitiveProductFixedSubring B ρ →
      IsDomain A ∧
      Function.Injective ((Pi.evalRingHom B i).comp f) ∧
      ((Pi.evalRingHom B i).comp f).range = transitiveStabilizerFixedSubring B ρ i ∧
      ∀ (K : Type k) [Field K] [Algebra A K] [IsFractionRing A K]
        (L : Type l) [Field L] [Algebra (B i) L] [IsFractionRing (B i) L],
        ∃ v : K →+* L,
          v.comp (algebraMap A K) =
            (algebraMap (B i) L).comp ((Pi.evalRingHom B i).comp f) ∧
          (∀ v' : K →+* L,
            v'.comp (algebraMap A K) =
              (algebraMap (B i) L).comp ((Pi.evalRingHom B i).comp f) → v' = v) ∧
          Set.range v = {x : L | ∀ (h : H) (hi : h • i = i),
            IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L)
              ((ρ h i).trans (RingEquiv.cast (R := B) hi)) x = x}) := by
  sorry

end RingTheory
