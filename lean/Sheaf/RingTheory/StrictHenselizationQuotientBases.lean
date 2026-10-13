/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
import Sheaf.RingTheory.BasisIffBasisQuotientOfNilpotent
import Sheaf.RingTheory.StrictHenselizationFaithfullyFlat
import Sheaf.RingTheory.StrictHenselizationTriples

/-!
# Fixed bases for strict henselization quotients

Source: Stacks Project, More on Algebra, Tag 07QM(4) and the proof of Tag 06LJ(c)
(blueprint: lem-sc-strict-henselization-quotient-bases).
-/

@[expose] public section

universe u

namespace Algebra

/-- Fixed residue-field lifts are bases of every positive-power quotient.
Source: Stacks Project, Tag 07QM(4), using Tag 051F and flat base change Tag 00HI.
(blueprint: lem-sc-strict-henselization-quotient-bases).

Proof: At the closed point of Spec A, identify the scheme residue field with A/n.
A pointed etale A-algebra S -> K determines the triple with prime ker(S -> K)
and the induced residue embedding into K; conversely the triple gives that map.
These constructions identify the diagrams defining IsStrictHenselization and the
triples colimit. Uniqueness of colimits transports the triples properties to C.
Choose a basis of K over A/n. The transported residue map identifies C/nC with K
and makes C local; lift the basis vectors through that surjective map. Faithful flatness
of strict henselization makes C flat over A. For each positive r, mapping ideal
powers gives (n C)^r = n^r C. Consequently C/(n C)^r is a flat A/n^r-module by
flat base change. The local ring A/n^r has nilpotent maximal ideal n/n^r; reducing
this module modulo that ideal gives K, and the fixed lifts give its chosen basis.
Apply Module.basis_iff_basisQuotient_of_nilpotent to obtain a basis on those lifts.
Invert its representation map and restrict scalars to A to obtain e r, which
sends each standard generator to the image of the fixed lift. The same lifts work
for every r. No completion comparison is asserted here.
-/
theorem strictHenselization_quotient_bases
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    ∃ (X : Type u) (x : X → C)
      (e : ∀ (r : ℕ), 1 ≤ r →
        (X →₀ A ⧸ (IsLocalRing.maximalIdeal A) ^ r) ≃ₗ[A]
          C ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r),
      (∀ (r : ℕ) (hr : 1 ≤ r) (i : X),
        e r hr (Finsupp.single i 1) =
          Ideal.Quotient.mk (((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r)
            (x i)) := by
  sorry

end Algebra
