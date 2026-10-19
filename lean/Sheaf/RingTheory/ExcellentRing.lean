/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Excellent and quasi-excellent rings

Source: Stacks Project, More on Algebra, Tags 07QT and 07P7; Algebra, Tags 00NI and
00NL (blueprint: def-exc-excellent-ring).

## Main definitions

* `IsQuasiExcellent` is the quasi-excellent predicate.
* `IsExcellent` is the excellent predicate.
* `IsCatenaryRing` and `IsUniversallyCatenary` encode the chain conditions used by
  the excellent predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A finite chain of prime ideals from `p` to `q`, of length `n`. Source: Stacks
Project, Algebra, Definition 00NI (blueprint: def-exc-excellent-ring). -/
def IsPrimeChain (A : Type u) [CommRing A] (p q : Ideal A) (n : ℕ)
    (c : Fin (n + 1) → Ideal A) : Prop :=
  (∀ i : Fin (n + 1), (c i).IsPrime) ∧
    c 0 = p ∧ c ⟨n, Nat.lt_succ_self n⟩ = q ∧ ∀ i : Fin n, c i.castSucc < c i.succ

/-- A saturated finite chain of prime ideals from `p` to `q`. Source: Stacks Project,
Algebra, Definition 00NI (blueprint: def-exc-excellent-ring). -/
def IsSaturatedPrimeChain (A : Type u) [CommRing A] (p q : Ideal A) (n : ℕ)
    (c : Fin (n + 1) → Ideal A) : Prop :=
  IsPrimeChain A p q n c ∧
    ∀ i : Fin n, ¬ ∃ r : Ideal A, r.IsPrime ∧ c i.castSucc < r ∧ r < c i.succ

/-- A commutative ring is catenary when every interval of prime ideals has a finite
upper bound on finite chain lengths and all saturated chains in that interval have the
same length. Source: Stacks Project, Algebra, Definition 00NI (blueprint:
def-exc-excellent-ring). -/
def IsCatenaryRing (A : Type u) [CommRing A] : Prop :=
  ∀ (p q : Ideal A) [p.IsPrime] [q.IsPrime], p ≤ q →
    (∃ N : ℕ, ∀ (n : ℕ) (c : Fin (n + 1) → Ideal A),
      IsPrimeChain A p q n c → n ≤ N) ∧
      ∀ (n m : ℕ) (c : Fin (n + 1) → Ideal A) (d : Fin (m + 1) → Ideal A),
        IsSaturatedPrimeChain A p q n c → IsSaturatedPrimeChain A p q m d → n = m

/-- A commutative ring is universally catenary when it is Noetherian and every finite
type algebra over it is catenary. Source: Stacks Project, Algebra, Definition 00NL (blueprint:
def-exc-excellent-ring). -/
def IsUniversallyCatenary (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A], IsCatenaryRing A

/-- A commutative ring is quasi-excellent when it is Noetherian, a G-ring, and every
finite type algebra has open regular locus. Source: Stacks Project, More on Algebra,
Definition 07QT and Definition 07P7 (blueprint: def-exc-excellent-ring). -/
def IsQuasiExcellent (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ IsGRing R ∧
    ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A],
      IsOpen {p : PrimeSpectrum A | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- A commutative ring is excellent when it is quasi-excellent and universally
catenary. Source: Stacks Project, More on Algebra, Definition 07QT and Algebra,
Definition 00NL (blueprint: def-exc-excellent-ring). -/
def IsExcellent (R : Type u) [CommRing R] : Prop :=
  IsQuasiExcellent R ∧ IsUniversallyCatenary R
