/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ExcellentRing
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.JTwoResidueFieldCriterion

/-!
# Fields are J-2 rings

Source: Stacks Project, More on Algebra, Tag 07PJ(1), the field case of the J-2 property
(blueprint: lem-per-field-j2).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- Every field has the J-2 property: each finite type algebra over it has open regular locus.

Source: Stacks Project, More on Algebra, Tag 07PJ(1), with the J-2 clause expanded as in
Tag 07P7, Definition J (blueprint: lem-per-field-j2).

Proof:
1. A field is Noetherian because its only ideals are the zero and unit ideals, both finitely
   generated.
2. For a prime of the field and a finite purely inseparable residue-field extension `L`, the
   prime is zero and the residue field is the field itself. Taking `L` as the finite model gives
   an algebra finite over the field, with fraction field `L`; its one-point spectrum is regular,
   so the whole spectrum is a nonempty open regular locus.
3. These finite-model properties satisfy the hypotheses of
   `lem-exc-j2-residue-field-criterion`, yielding the J-2 property.
4. Expanding the J-2 clause in `def-exc-excellent-ring` gives the displayed open regular locus
   for every finite type algebra.
-/
theorem isJTwo_of_field (k : Type u) [Field k] :
    ∀ (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B],
      IsOpen {p : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime p.asIdeal)} := by
  sorry
