/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.Irreducible
public import WeilConjectures.RingTheory.EssentiallySmooth
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn

/-!
# Smooth local maps preserve geometric unibranchness

Source: Stacks Project, `literature/stacks-project/more-algebra.tex`, Tag 0DQ1
(lemma-invariance-number-branches-smooth), part (1), with Tag 0C37, part (3)
(blueprint: lem-dl-a1-smooth-local-branch-invariance).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A local essentially smooth map preserves irreducibility of strict henselizations.

Source: Stacks Project, `literature/stacks-project/more-algebra.tex`, Tag 0DQ1,
part (1), with Tag 0C37, part (3) (blueprint: lem-dl-a1-smooth-local-branch-invariance).

Proof:
1. Use the strict-henselization base-change statement (Tag 08HV) to replace the
   base and target by compatible strict localizations, preserving essential
   smoothness by base change and composition.
2. Replace the strictly henselian base by its quotient by its unique minimal
   prime, using the irreducible-components/minimal-primes characterization and
   preservation of strict henselianity under this quotient.
3. Flatness of smooth maps, localizations, and strict henselizations, together
   with faithful flatness of a flat local map, gives the required nonzero flat
   base change.
4. Tensor the resulting strict henselization with the integral closure of the
   base domain. Smooth and etale base change preserve normality, filtered
   colimits preserve normality, and the purely inseparable residue extension
   makes this tensor local. Hence it is a domain, and faithful flatness reflects
   that domain property back to the strict henselization.
5. The unique-minimal-prime characterization then gives irreducibility of the
   target strict henselization.
-/
theorem smooth_local_branch_invariance
    (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hEss : Algebra.EssentiallySmooth A B)
    (hgeom : ∀ (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField A) K]
      [IsSepClosure (IsLocalRing.ResidueField A) K]
      [Algebra A K]
      [IsScalarTower A (IsLocalRing.ResidueField A) K]
      [CommRing H] [Algebra A H],
      Algebra.StrictHenselizationPresentationIn.{u, v} A K H →
        IrreducibleSpace (PrimeSpectrum H)) :
    ∀ (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField B) K]
      [IsSepClosure (IsLocalRing.ResidueField B) K]
      [Algebra B K]
      [IsScalarTower B (IsLocalRing.ResidueField B) K]
      [CommRing H] [Algebra B H],
      Algebra.StrictHenselizationPresentationIn.{u, v} B K H →
        IrreducibleSpace (PrimeSpectrum H) := by
  sorry

end AlgebraicGeometry
