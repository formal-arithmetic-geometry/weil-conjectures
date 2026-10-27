/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal

/-! # Integral closure with geometrically normal scalar extensions

Source: Stacks Project, varieties.tex, Tag 0C3N,
lemma-normalization-and-change-of-fields, affine normal-tensor comparison;
algebra.tex, Tags 034M and 0307, with the node's explicit compatibility refinement
(blueprint: lem-sfb-integral-closure-geonormal-scalar-extension).
-/

@[expose] public section
set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace integralClosure

/-- A finite geometrically normal normalization of a geometrically integral finite type
algebra stays the normalization after every field extension. The maps are characterized
by their fraction formula. Field maps extend to fraction fields and commute with these
embeddings. Principal localization gives the same embeddings in the common fraction
field, with exactly the localized integral-closure images.

Here `B` is the actual subalgebra of the fraction ring, with `hB` specifying its carrier.
The last clause writes the localization square using the maps from `A[1/f]` and `B[1/f]`
into the common fraction field. Its generator equations determine these maps uniquely,
since the inverted element has nonzero image. Thus no arbitrary comparison map is used.

Source: Stacks Project, varieties.tex, Tag 0C3N,
lemma-normalization-and-change-of-fields, affine normal-tensor comparison;
algebra.tex, Tags 034M and 0307, and the node's compatibility refinement
(blueprint: lem-sfb-integral-closure-geonormal-scalar-extension).

Proof:
1. Fix L and put C = A tensor L, D = B tensor L, E = Frac(C). Flatness of L over k
   (lem-weil-pbc-module-over-field-flat) and flat preservation of injections
   (lem-trf-flat-tensor-preserves-injection) give C inside D inside Frac(A) tensor L.
   By lem-weil-pbc-localization-tensor-over-base the last ring is the localization of C
   at the nonzero elements of A. The map A to C is injective, by tensoring a k-linear
   retraction of k to L. Since C is a domain, its localization embeds into E. This
   constructs j and gives the displayed fraction equation. Tensor multiplication and
   its universal property are lem-weil-pbc-algebra-tensor-pushout-universal-property.
2. Tensor the finite A-module generators of B with 1. They generate D over C, so
   lem-weil-pbc-finite-algebra-is-integral puts the image of D in the integral closure.
3. The inclusions C inside D inside E make D a domain with fraction field E.
   By lem-weil-pbc-spec-domain-stalks-function-field, the assumed normal local rings
   are the prime localizations of D. Apply
   lem-weil-pbc-normal-ring-integrally-closed-total to conclude integral closedness.
4. An element of E integral over C is also integral over D. It therefore belongs
   to D. This proves the reverse inclusion and the integral-closure equality.
5. For a k-field homomorphism t : L to M, tensoring a linear retraction of t gives
   injectivity of A tensor L to A tensor M. Extend to fraction fields. Both composites
   on b tensor l have fraction (a tensor t(l))/(s tensor 1) when b = a/s, so they
   agree. This also proves compatibility for identities and composites.
6. For nonzero f, apply lem-weil-pbc-integral-closure-commutes-localization both to
   A inside Frac(A) and C inside E. The identifications of
   lem-weil-pbc-algebra-localization-away-base-change identify the localized tensors.
   Their embeddings into E extend j and send (b/f^n) tensor l to
   j(b tensor l)/(f tensor 1)^n. These formulas prove the localization square and
   its compatibility with the field maps simultaneously.
-/
theorem geonormal_scalar_extension
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    (hft : RingHom.FiniteType (algebraMap k A))
    (B : Subalgebra A (FractionRing A)) (hB : B = integralClosure A (FractionRing A))
    [Module.Finite A B]
    (hgi : ∀ (L : Type (max u v w)) [Field L] [Algebra k L], IsDomain (A ⊗[k] L))
    (hgn : ∀ (L : Type (max u v w)) [Field L] [Algebra k L]
      (p : Ideal (B ⊗[k] L)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∃ j : ∀ (L : Type (max u v w)) [Field L] [Algebra k L],
        B ⊗[k] L →ₐ[k] FractionRing (A ⊗[k] L),
      (∀ (L : Type (max u v w)) [Field L] [Algebra k L],
        Function.Injective (j L) ∧
        (∀ x : FractionRing (A ⊗[k] L),
          (∃ b : B ⊗[k] L, j L b = x) ↔ IsIntegral (A ⊗[k] L) x) ∧
        IsDomain (B ⊗[k] L) ∧ IsIntegrallyClosed (B ⊗[k] L) ∧
        RingHom.Finite (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom k A B) (AlgHom.id k L)).toRingHom ∧
        (∀ (b : B) (a s : A), s ≠ 0 →
          (b : FractionRing A) * algebraMap A (FractionRing A) s =
            algebraMap A (FractionRing A) a →
          ∀ l : L, j L (b ⊗ₜ[k] l) *
            algebraMap (A ⊗[k] L) (FractionRing (A ⊗[k] L)) (s ⊗ₜ[k] (1 : L)) =
            algebraMap (A ⊗[k] L) (FractionRing (A ⊗[k] L)) (a ⊗ₜ[k] l))) ∧
      (∀ (L M : Type (max u v w)) [Field L] [Field M] [Algebra k L] [Algebra k M]
        (t : L →ₐ[k] M),
        ∃ q : FractionRing (A ⊗[k] L) →ₐ[k] FractionRing (A ⊗[k] M),
          (∀ c : A ⊗[k] L,
            q (algebraMap (A ⊗[k] L) (FractionRing (A ⊗[k] L)) c) =
              algebraMap (A ⊗[k] M) (FractionRing (A ⊗[k] M))
                (Algebra.TensorProduct.map (AlgHom.id k A) t c)) ∧
          (∀ d : B ⊗[k] L,
            q (j L d) = j M (Algebra.TensorProduct.map (AlgHom.id k B) t d))) ∧
      (∀ (L : Type (max u v w)) [Field L] [Algebra k L] (f : A), f ≠ 0 →
        ∃ (aLoc : Localization.Away f ⊗[k] L →ₐ[k] FractionRing (A ⊗[k] L))
          (bLoc : Localization.Away (algebraMap A B f) ⊗[k] L →ₐ[k]
            FractionRing (A ⊗[k] L)),
          Function.Injective aLoc ∧ Function.Injective bLoc ∧
          (∀ (a : A) (l : L),
            aLoc (algebraMap A (Localization.Away f) a ⊗ₜ[k] l) =
              algebraMap (A ⊗[k] L) (FractionRing (A ⊗[k] L)) (a ⊗ₜ[k] l)) ∧
          (∀ (b : B) (l : L),
            bLoc (algebraMap B (Localization.Away (algebraMap A B f)) b ⊗ₜ[k] l) =
              j L (b ⊗ₜ[k] l)) ∧
          (∀ x : FractionRing (A ⊗[k] L),
            (∃ b : Localization.Away (algebraMap A B f) ⊗[k] L, bLoc b = x) ↔
              aLoc.toRingHom.IsIntegralElem x)) := by
  sorry

end integralClosure
