/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # A weakly unramified local unit-root cover of a DVR diagram

Source: Stacks Project, Tag 0BRM, the first claim in its proof.
(blueprint: lem-sbc-dvr-unit-root-generation) -/

@[expose] public section

universe u
namespace RingTheory

/-- Adjoining a root of a unit simultaneously above the two DVRs of a local diagram.

Source: Stacks Project, Tag 0BRM, the paragraph beginning with the claim that the
unit can be assumed to be an e-th power.
(blueprint: lem-sbc-dvr-unit-root-generation)

Proof: Form C = A[X]/(X^e-v). Its root is a unit, and e is a unit, so its derivative
is a unit. Thus C is finite etale over A. Form D = T tensor_A C, which is finite
etale over T. Choose a maximal ideal of D above the maximal ideal of T and contract
it to a prime of C. Localize D and C at these primes, obtaining T' and A'. These
are DVR domains: an etale local extension of a DVR is regular of dimension one.
Both maps are local and their square commutes. Since A -> A' is essentially
etale, the extension of its maximal ideal is the maximal ideal of A'. The image r
of X satisfies r^e = v. Take F' = Frac(T').
The
injection T -> T' extends uniquely to a field map iF from F = Frac(T), and the
localization map A' -> T' -> F' is compatible with A. The field F' is the selected
field factor of F[X]/(X^e-v). Hence it is generated as an F-algebra by the root:
the root is algebraic, so this algebra is already a field. Since r belongs to A',
F' is generated as an A'-algebra by iF(F). This construction does not use any
ramification or residue-separability assumption on T/A. For e = 1 use A, T and F
itself, with r = v. -/
theorem dvr_unit_root_weakly_unramified_diagram
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (e : ℕ) (hepos : 0 < e) (he : IsUnit (e : A)) (v : Aˣ)
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    (F : Type u) [Field F] [Algebra A F] [Algebra T F]
    [IsFractionRing T F] [IsScalarTower A T F] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A')
      (_ : IsDiscreteValuationRing A') (aAA' : Algebra A A'),
    letI := aAA'
    ∃ (hAA' : IsLocalHom (algebraMap A A')) (r : A'),
    letI := hAA'
    r ^ e = algebraMap A A' (v : A) ∧
    (IsLocalRing.maximalIdeal A).map (algebraMap A A') = IsLocalRing.maximalIdeal A' ∧
    ∃ (T' : Type u) (_ : CommRing T') (_ : IsDomain T')
      (_ : IsDiscreteValuationRing T') (aTT' : Algebra T T') (aA'T' : Algebra A' T'),
    letI := aTT'
    letI := aA'T'
    ∃ (_ : IsLocalHom (algebraMap T T')) (_ : IsLocalHom (algebraMap A' T')),
    (∀ a : A, algebraMap T T' (algebraMap A T a) =
      algebraMap A' T' (algebraMap A A' a)) ∧
    ∃ (F' : Type u) (_ : Field F') (aA'F' : Algebra A' F') (aT'F' : Algebra T' F'),
    letI := aA'F'
    letI := aT'F'
    ∃ (_ : IsFractionRing T' F') (_ : IsScalarTower A' T' F') (iF : F →+* F'),
    (∀ a : A, iF (algebraMap A F a) = algebraMap A' F' (algebraMap A A' a)) ∧
    (∀ t : T, iF (algebraMap T F t) = algebraMap T' F' (algebraMap T T' t)) ∧
    Algebra.adjoin A' (Set.range iF) = ⊤ := by sorry

end RingTheory
