/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Finite birational algebras after flat scalar extension

Source: Stacks Project, `varieties.tex`, Tag 0C3V, proof of
`lemma-normalization-same-after-completion`; agent-explicit common-denominator
argument for arbitrary flat scalar extension, as recorded in the DAG
(blueprint: lem-trf-flat-birational-normalization-comparison).

The tensor factors are in the standard base-change order `R ⊗[A] B`, canonically
commuted from the node's `B ⊗[A] R`. The structural map `f` is `algebraMap A R`.
`FractionRing` localizes at all non-zero-divisors, even for the zero ring.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open scoped TensorProduct

namespace RingTheory

/-- Canonical comparison, common denominators, and normalization after flat base change.

Source: Stacks Project, `varieties.tex`, Tag 0C3V, integral-closure comparison in the
proof of `lemma-normalization-same-after-completion`; the arbitrary-flat-base-change
calculation is agent-written (blueprint: lem-trf-flat-birational-normalization-comparison).

Proof:
1. A regular denominator cannot annihilate a nonzero element, so every ring embeds in
   its total fractions. Flatness preserves the injective multiplication-by-t map on A
   (`lem-trf-flat-tensor-preserves-injection`), hence f sends regular elements to regular
   elements. Localization's universal property
   (`lem-weil-pbc-ring-localization-universal-property`) supplies the unique fraction map.
2. For finite generators b_h = a_h/t_h, the product s of their regular denominators is
   regular. Each s*b_h belongs to A, and linear combinations give s*B contained in A.
   Multiplication by s is injective on B, since s is a unit in Q(A).
3. Base-change the injective linear map d : B to A, b to s*b, using
   `def-weil-module-base-change`. Flatness preserves its injectivity and that of
   multiplication by s on B. The pure-tensor identities give i(dR(c)) = f(s)*c and
   dR(i(r)) = f(s)*r. The second identity and regularity of f(s) prove i injective.
4. The balanced formula phi(b)*r induces j by `def-weil-pbc-module-tensor-product`.
   On pure tensors it preserves multiplication and one, hence it is an R-algebra map.
   Also f(s)*j(c) = dR(c)/1, so j(c) = dR(c)/f(s), lying in R[1/f(s)].
   If j(c) = 0, injectivity of R into Q(R) and of dR gives c = 0.
5. Every regular element of R stays regular on C, by the embedding j. For regular t
   in C, i(dR(t)) = f(s)*t implies dR(t) is regular in R: if dR(t)*r = 0,
   injectivity of i and regularity of t and f(s) force r = 0. Thus j(t) is a unit.
6. Localization's universal property extends j to J : Q(C) to Q(R), and i to
   H : Q(R) to Q(C). Agreement on R gives JH = 1. The denominator identities give
   HJ(c/1) = c/1; localization uniqueness gives HJ = 1. Their fraction formula is
   J(c/t) = dR(c)/dR(t), independently of the chosen generators and denominators.
7. The b_h tensor 1 generate C over R (`def-weil-finitely-generated-module`), so C
   is finite and then integral by `lem-weil-pbc-finite-algebra-is-integral`.
   Applying j to monic equations puts j(C) in the integral closure of R in Q(R).
8. If C is integrally closed in Q(C), transfer a monic equation for x in Q(R)
   along H. Then H(x) is integral over C, so belongs to C by
   `def-weil-pbc-integral-closure`. Applying J gives x in j(C), proving equality.
-/
theorem flat_finite_birational_normalization_comparison
    (A : Type u) (R : Type v) [CommRing A] [CommRing R]
    [IsReduced A] [IsReduced R] [Algebra A R]
    (hf : (algebraMap A R).Flat)
    (B : Subalgebra A (FractionRing A)) [Module.Finite A B] :
    ∃ hregular : nonZeroDivisors A ≤ (nonZeroDivisors R).comap (algebraMap A R),
      (∀ (a : A) (t : nonZeroDivisors A),
        IsLocalization.map (FractionRing R) (algebraMap A R) hregular
            (IsLocalization.mk' (FractionRing A) a t) =
          IsLocalization.mk' (FractionRing R) (algebraMap A R a)
            (⟨algebraMap A R t, hregular t.property⟩ : nonZeroDivisors R)) ∧
      (∀ ψ : FractionRing A →+* FractionRing R,
        (∀ a : A, ψ (algebraMap A (FractionRing A) a) =
          algebraMap R (FractionRing R) (algebraMap A R a)) →
        ψ = IsLocalization.map (FractionRing R) (algebraMap A R) hregular) ∧
      ∃ (j : R ⊗[A] B →ₐ[R] FractionRing R)
        (J : FractionRing (R ⊗[A] B) ≃+* FractionRing R),
        (∀ (b : B) (r : R), j (r ⊗ₜ[A] b) =
          IsLocalization.map (FractionRing R) (algebraMap A R) hregular
            (b : FractionRing A) * algebraMap R (FractionRing R) r) ∧
        Function.Injective j ∧
        Function.Injective (algebraMap R (R ⊗[A] B)) ∧
        (∀ c : R ⊗[A] B,
          J (algebraMap (R ⊗[A] B) (FractionRing (R ⊗[A] B)) c) = j c) ∧
        (IsIntegrallyClosedIn (R ⊗[A] B) (FractionRing (R ⊗[A] B)) →
          j.range = integralClosure R (FractionRing R)) ∧
        (∀ (n : ℕ) (b : Fin n → B) (a : Fin n → A) (t : Fin n → nonZeroDivisors A),
          Submodule.span A (Set.range b) = ⊤ →
          (∀ h : Fin n, (b h : FractionRing A) =
            IsLocalization.mk' (FractionRing A) (a h) (t h)) →
          ∀ s : nonZeroDivisors A, s = ∏ h : Fin n, t h →
          Function.Injective (fun r : R => algebraMap A R s * r) ∧
          Function.Injective (fun c : R ⊗[A] B => algebraMap A R s • c) ∧
          ∃ (d : B →ₗ[A] A) (dR : R ⊗[A] B →ₗ[R] R),
            (∀ x : B, algebraMap A (FractionRing A) (d x) =
              algebraMap A (FractionRing A) s * (x : FractionRing A)) ∧
            dR = (TensorProduct.AlgebraTensorModule.rid A R R).toLinearMap.comp
              (d.baseChange R) ∧
            (∀ (x : B) (r : R), dR (r ⊗ₜ[A] x) = algebraMap A R (d x) * r) ∧
            (∀ c : R ⊗[A] B, algebraMap R (R ⊗[A] B) (dR c) =
              algebraMap A R s • c) ∧
            (∀ r : R, dR (algebraMap R (R ⊗[A] B) r) = algebraMap A R s * r) ∧
            (∀ c : R ⊗[A] B, j c = IsLocalization.mk' (FractionRing R) (dR c)
              (⟨algebraMap A R s, hregular s.property⟩ : nonZeroDivisors R)) ∧
            (∀ c : R ⊗[A] B, ∃ z : Localization.Away (algebraMap A R s),
              IsLocalization.map (M := Submonoid.powers (algebraMap A R s))
                (T := nonZeroDivisors R) (FractionRing R) (RingHom.id R)
                (Submonoid.powers_le.mpr (hregular s.property)) z = j c) ∧
            (∀ (c : R ⊗[A] B) (tC : nonZeroDivisors (R ⊗[A] B)),
              ∃ ht : dR tC ∈ nonZeroDivisors R,
                J (IsLocalization.mk' (FractionRing (R ⊗[A] B)) c tC) =
                  IsLocalization.mk' (FractionRing R) (dR c)
                    (⟨dR tC, ht⟩ : nonZeroDivisors R))) := by
  sorry

end RingTheory
