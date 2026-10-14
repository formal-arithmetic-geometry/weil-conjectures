/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # The algebraic tame root calculation in a generic tensor factor

Source: Stacks Project, Tags 09EV, 09EB, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-galois-root-factor-uniformizer) -/

@[expose] public section

universe u
open scoped TensorProduct
namespace RingTheory

/-- The root generates the maximal ideal of an integral-closure local factor.

Source: Stacks Project, Tags 09EV, 09EB, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-galois-root-factor-uniformizer)

Proof: Write K = Frac(B), A = B[t]/(t^n-pi), and F = (E tensor_B A)/P.
For n > 1, 09EV makes A a DVR with uniformizer t, fraction field K1, and
ramification index n over B. For n = 1 evaluation identifies A with B.
Since pi is invertible in E, E tensor_B A is E tensor_K K1. It is a finite
product of fields, as E/K is finite separable. Thus F is one such field.
The integral closure of B in E has DVR local rings at its primes above (pi).
By 09EB their ramification index and residue degree divide [E:K], hence n.
Invertibility of n forces the ramification index to be prime to the residue
characteristic and the residue inseparable degree to be one. Apply 0BRM to
these tame DVR extensions and K1/K: every local ring of the integral closure
of A in F above (t) is adically formally smooth over A. By 09E7 its index is
one. Since t is a uniformizer of A, its image generates the local maximal ideal.
All maps used here are the structural maps induced by the right tensor inclusion. No finiteness
of a scheme normalization is assumed. Degree-one extensions and n = 1 give
the same index-one conclusion. -/
theorem dvr_galois_root_factor_uniformizer
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (hn : IsUnit (n : B))
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧
      IsGalois (FractionRing B) E ∧ Module.finrank (FractionRing B) E ∣ n) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    let D := E ⊗[B] A
    ∀ (P : Ideal D) (hP : P.IsMaximal),
    letI := hP
    let F := D ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
    letI := alpha.toAlgebra
    let S := integralClosure A F
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    letI := hQ
    Q.comap (algebraMap A S) = Ideal.span
      {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} →
    let t := algebraMap S (Localization.AtPrime Q)
      (algebraMap A S
        (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)))
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) = Ideal.span {t} := by sorry

end RingTheory
