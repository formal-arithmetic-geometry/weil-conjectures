/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Profinite
import Sheaf.RepresentationTheory.DvrGaloisComparison
import Sheaf.RepresentationTheory.DvrGaloisProcyclic

/-!
# Prime-to-characteristic local Galois cohomology

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
  sk-prop-a1-kummer/lem-exc-dvr-galois.md and its proof file;
Stacks Project, Tag 09E3 (blueprint: lem-exc-dvr-galois).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

set_option warningAsError true in
/-- (blueprint: lem-exc-dvr-galois) Let `R` be an excellent strictly henselian DVR
with algebraically closed residue field of positive characteristic `p`. For a finite
prime-power-torsion coefficient ring at a different prime `ell`, continuous cohomology
of every discrete module for the absolute Galois group of `Frac R` vanishes above
degree one; for finite modules its degree-zero and degree-one groups are finite.

Proof:
1. Strict henselianity gives henselianity (`def-weil-pbc-henselian-terminology`). Apply
   `lem-exc-henselian-dvr-tame-sequence` to obtain a continuous surjection from G to
   the product of the additive r-adic groups for primes r different from p, with
   closed normal pro-p kernel P.
2. Let H be the kernel of its ell-coordinate. Then H/P is the product over primes
   different from p and ell, and G/H is the additive ell-adic group. In each finite
   quotient Q of H, the image of P is a p-group and the remaining quotient factors
   through a finite product of r-power cyclic groups with r different from ell.
   Thus the order of Q is prime to ell. Compact Hausdorff quotient maps give the
   claimed topological quotient identifications.
3. The functor V(N) = N^H is additive and preserves kernels. For an invariant y
   under a surjection, choose a lift x. Its finite H-orbit spans a finite A-module
   L. The intersection of stabilizers of elements of L is open normal in H, so
   the action factors through a finite quotient Q. Choose integers a,b with
   a|Q| + b ell^s = 1. Then a times the sum of the Q-translates of x is H-fixed
   and maps to y. This proves exactness, detected on underlying modules by
   `lem-exc-discrete-modules-abelian`.
4. Inflation from G/H to G preserves monomorphisms and is left adjoint to V:
   an equivariant map from an inflated module factors uniquely through H-fixed
   elements. Transport an injective lifting problem through this adjunction and
   solve it using `def-sp-injective-resolutions`; hence V preserves injectives.
5. Apply V to an injective resolution of M. Exactness and preservation of
   injectives give a resolution of M^H, and the complexes of G-invariants and
   successive H- and G/H-invariants coincide termwise. By
   `def-exc-continuous-cohomology` and `def-sp-left-exact-additive`, this computes
   the same cohomology. Relabel G/H as the additive ell-adic group.
6. Apply `lem-exc-procyclic-two-term` to M^H and generator 1. The two-term
   complex with differential tau - 1 vanishes outside degrees zero and one,
   giving the asserted higher vanishing. If M is finite, M^H is finite, as are
   the kernel and cokernel of that differential, giving both finiteness clauses.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer/
lem-exc-dvr-galois and its six DAG proof steps; Stacks Project, More on Algebra,
Tag 09E3 (blueprint: lem-exc-dvr-galois). -/
theorem isZero_dvr_galois_cohomology
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : IsExcellent R) [IsStrictlyHenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ p)
    (A : Type v) [Ring A] [Finite A]
    (hA : ∃ s : ℕ, (ell ^ s : ℕ) • (1 : A) = 0)
    (M : DiscreteContinuousRep.{v, u, max u w} A
      (Gal(SeparableClosure (FractionRing R)/FractionRing R))) :
    (∀ q : ℕ, 1 < q →
      IsZero ((discreteContinuousCohomologyFunctor
        (Gal(SeparableClosure (FractionRing R)/FractionRing R)) A q).obj M)) ∧
      (Finite M.obj.V →
        Finite (((discreteContinuousCohomologyFunctor
          (Gal(SeparableClosure (FractionRing R)/FractionRing R)) A 0).obj M).carrier) ∧
          Finite (((discreteContinuousCohomologyFunctor
            (Gal(SeparableClosure (FractionRing R)/FractionRing R)) A 1).obj M).carrier)) := by
  obtain ⟨s, hs⟩ := hA
  obtain ⟨N, hMN, hcomp⟩ := nonempty_dvr_galois_cohomology_iso
    R hR p ell hell A ⟨s, hs⟩ M
  have hpro := procyclic_cohomology_conclusions ell s A hs N
  constructor
  · intro q hq
    obtain ⟨e⟩ := hcomp q
    exact IsZero.of_iso (hpro.1 q hq) e
  · intro hM
    have hN : Finite N.obj.V := hMN hM
    exact ⟨by
      obtain ⟨e⟩ := hcomp 0
      have : Finite (((discreteContinuousCohomologyFunctor
          (Multiplicative ℤ_[ell]) A 0).obj N).carrier) :=
        (hpro.2 hN).1
      exact Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm,
      by
        obtain ⟨e⟩ := hcomp 1
        have : Finite (((discreteContinuousCohomologyFunctor
            (Multiplicative ℤ_[ell]) A 1).obj N).carrier) :=
          (hpro.2 hN).2
        exact Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm⟩

end Rep
