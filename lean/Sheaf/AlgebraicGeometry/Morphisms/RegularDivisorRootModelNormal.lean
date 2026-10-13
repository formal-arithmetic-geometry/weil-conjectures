/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

/-! Normality of full root algebras along a regular divisor. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Full root models of a regular divisor have normal domain stalks.

Source: Stacks Project, Tag 0EYH, local ring verification in its proof;
Tag 0EYG, the full root algebra in the strictly henselian calculation.
(blueprint: lem-sbc-regular-divisor-root-model-normal)

Proof: Each monic root algebra B=R[T]/(T^e-f) is finite free over the
Noetherian R, hence Noetherian. Multiplication by f on B is injective by
freeness. Since t^e=f, multiplication by t is injective too. At a prime
containing t, the quotient of the localized B by t is a localization of
R/(f), hence regular. A Noetherian local ring whose quotient by a
nonzerodivisor is regular is regular itself. At a prime not containing t,
f and the derivative e*t^(e-1) are units. The localized root algebra is
therefore etale over the regular base and is regular. Regular local rings
are integrally closed domains. Every prime of a finite product comes from
one factor, with the same local ring. Identify the scheme stalk with this
localization to obtain the assertion. For m=0 there are no spectrum points,
so the conclusion is vacuous; the argument also allows zero R and unit f. -/
theorem regular_divisor_root_model_normal
    (R : CommRingCat.{u}) [IsRegularRing R] (m : ℕ) (f : R)
    (hf : IsSMulRegular R f) [IsRegularRing (R ⧸ Ideal.span {f})]
    (e : Fin m → ℕ) (he : ∀ k, 0 < e k ∧ IsUnit (e k : R)) :
    let N := Spec (CommRingCat.of (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))
    ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z) := by sorry

end AlgebraicGeometry.Scheme
