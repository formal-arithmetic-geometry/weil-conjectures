/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Sheaf.RingTheory.DimOneResidueFieldsFinite
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite quotient fraction fields over a principal prime

Source: Stacks Project, Tags 032P and 031F, residue-field finiteness.
(blueprint: lem-weil-pbc-principal-prime-quotient-fraction-finite).
-/

@[expose] public section

universe uR uS uK uL
set_option autoImplicit false

attribute [local instance] FractionRing.liftAlgebra

/-- A prime over a principal prime in a finite extension of fraction fields has
finite quotient fraction field extension.
Source: Stacks Project, Tag 032P, localization and application of Tag 031F.
(blueprint: lem-weil-pbc-principal-prime-quotient-fraction-finite).

Proof: If x = 0, the contraction of Q is zero. Localizing S at the nonzero
 elements of R gives a K-subalgebra of L. Each element is algebraic over K,
 so this domain is a field. Consequently the only prime over zero is zero,
 and the quotient fraction fields identify with K and L. If x is nonzero,
 the principal prime xR has height one by the principal ideal theorem and
 the strict chain (0) < xR. Its localization is a one-dimensional Noetherian
 local domain. Localize S at Q; the fraction fields are still K and L,
 and the localized maximal ideal contracts to the base maximal ideal.
 Apply Tag 031F to obtain a finite extension of residue fields. For any
 prime ideal, its residue field is a fraction field of the quotient domain.
 Transport the finite-dimensionality along the canonical equivalences with
 the fraction fields of R/(Q ∩ R) and S/Q. No integrality or normality of S
 is needed for this residue-field argument. -/
theorem principal_prime_quotient_fraction_finite
    (R : Type uR) (S : Type uS) (K : Type uK) (L : Type uL)
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [FiniteDimensional K L]
    (x : R) (Q : Ideal S) [Q.IsPrime]
    (hcontract : Q.comap (algebraMap R S) = Ideal.span ({x} : Set R)) :
    letI : FaithfulSMul (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
    FiniteDimensional (FractionRing (R ⧸ Q.comap (algebraMap R S)))
      (FractionRing (S ⧸ Q)) := by sorry
