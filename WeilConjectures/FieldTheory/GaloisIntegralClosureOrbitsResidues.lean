/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Basic
public import WeilConjectures.Mathlib.RingTheory.Invariant.Profinite
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.FieldTheory.Normal.Defs

/-! # Prime orbits and residue fields of a Galois integral closure

Source: Stacks Project, Tag 0BRK, `lemma-one-orbit-geometric-galois`, clauses (1) and (2)
(blueprint: lem-dl-a1-galois-integral-closure-orbits-residues).

The integral closure and its restricted Galois action are the existing constructions.
The residue assertion uses arbitrary fraction-field models of the two quotient domains.
Their scalar towers specify the canonical embedding induced by contraction, and the map
`IsFractionRing.stabilizerHom` is the canonical action on those fraction fields.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uR uK uE

open scoped Pointwise

namespace Ideal

/-- Primes of the integral closure with the same contraction form one Galois orbit.

Source: Stacks Project, Tag 0BRK, `lemma-one-orbit-geometric-galois` (1)
(blueprint: lem-dl-a1-galois-integral-closure-orbits-residues).

Proof: (1) By `lem-weil-pbc-finite-set-in-finite-galois-subextension`, every finite subset
of E is contained in a finite Galois intermediate field M. The integral closures S_M
therefore have union S. By `lem-weil-pbc-finite-galois-fixed-field`, their Galois groups
are finite and have fixed field K. Integral elements in K belong to R by normality, so
S_M has fixed ring R. (2) Apply `lem-dl-a1-finite-invariant-prime-orbits-residues` to the
two contracted primes in each S_M. The set T_M of automorphisms carrying one to the
other is finite and nonempty. (3) Normality makes restriction to M well defined
(`lem-sfb-normal-embeddings-automorphism-transitive`), and contraction makes restriction
carry T_N into T_M. The finite Galois intermediate fields form a nonempty directed set.
Apply `lem-trf-cofiltered-finite-sets-section` to these finite sets; surjectivity of the
transition maps is unnecessary. Assemble the compatible automorphisms using
`lem-exc-galois-krull-finite-limit`. Membership in either prime is detected at a finite
stage, so the assembled automorphism carries the first prime to the second. -/
theorem galoisIntegralClosure_prime_orbit
    {R : Type uR} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
    {E : Type uE} [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    [IsGalois K E]
    (t t' : Ideal (integralClosure R E)) [t.IsPrime] [t'.IsPrime]
    (h : t.under R = t'.under R) :
    ∃ g : Gal(E/K), g • t = t' := by
  let : IsIntegrallyClosedIn R K :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp inferInstance
  let : TopologicalSpace (integralClosure R E) := ⊥
  let : DiscreteTopology (integralClosure R E) := ⟨rfl⟩
  let : ContinuousSMul Gal(E/K) (integralClosure R E) :=
    Algebra.continuousSMul_integralClosure R K E
  let : Algebra.IsInvariant R (integralClosure R E) Gal(E/K) :=
    Algebra.isInvariant_integralClosure R K E
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := R) (B := integralClosure R E) (G := Gal(E/K)) t t' h
  exact ⟨g, hg.symm⟩

/-- Residue fields of a Galois integral closure are algebraic and normal, and their
base-field automorphisms lift to the decomposition group. The fields k and l are models
of Frac(R/p) and Frac(S/t); the scalar towers give the induced residue extension.

Source: Stacks Project, Tag 0BRK, `lemma-one-orbit-geometric-galois` (2)
(blueprint: lem-dl-a1-galois-integral-closure-orbits-residues).

Proof: (1) Use finite Galois intermediate fields M as in
`lem-weil-pbc-finite-set-in-finite-galois-subextension`, with S_M the integral closure of
R in M. The finite Galois fixed-field lemma identifies the invariant ring with R.
(2) `lem-dl-a1-finite-invariant-prime-orbits-residues` gives algebraic normal residue
extensions L_M/k and surjective residue actions of the finite decomposition groups.
(3) A fraction in l has a numerator and denominator lifted from S. A common finite
Galois stage contains both lifts, and a denominator nonzero modulo t stays nonzero at
that stage. Thus l is the union of the L_M. Algebraicity and splitting of each minimal
polynomial follow in a stage containing its element, proving algebraicity and normality.
(4) For an automorphism alpha of l/k, normality and
`lem-sfb-normal-embeddings-automorphism-transitive` show that alpha preserves every L_M.
Its restrictions are compatible, by injectivity of the residue-field embeddings.
(5) The sets U_M of finite-stage decomposition automorphisms inducing these restrictions
are finite and nonempty by the finite invariant-ring lemma. Contraction and the formula
on fractions make restriction carry U_N into U_M.
(6) `lem-trf-cofiltered-finite-sets-section` selects compatible lifts, and
`lem-exc-galois-krull-finite-limit` assembles them into g in Gal(E/K). Finite-stage
membership shows g stabilizes t; the fraction formula shows its residue action is alpha.
The canonical `IsFractionRing.stabilizerHom` respects products because its value on a
fraction is the fraction of the images of its numerator and denominator. No separability
or perfection of l/k is used. -/
theorem galoisIntegralClosure_residue_normal_surjective
    {R : Type uR} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
    {E : Type uE} [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    [IsGalois K E]
    (p : Ideal R) [p.IsPrime]
    (t : Ideal (integralClosure R E)) [t.IsPrime] [t.LiesOver p]
    (k : Type uR) (l : Type uE) [Field k] [Field l]
    [Algebra (R ⧸ p) k] [IsFractionRing (R ⧸ p) k]
    [Algebra (integralClosure R E ⧸ t) l] [IsFractionRing (integralClosure R E ⧸ t) l]
    [Algebra (R ⧸ p) l] [IsScalarTower (R ⧸ p) (integralClosure R E ⧸ t) l]
    [Algebra k l] [IsScalarTower (R ⧸ p) k l] :
    Algebra.IsAlgebraic k l ∧ Normal k l ∧
      Function.Surjective (IsFractionRing.stabilizerHom Gal(E/K) p t k l) := by
  sorry

end Ideal
