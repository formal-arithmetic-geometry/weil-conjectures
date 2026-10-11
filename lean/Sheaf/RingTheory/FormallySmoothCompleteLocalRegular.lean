/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Sheaf.RingTheory.FormallySmoothAdic
public import Sheaf.RingTheory.GRing

/-!
# Regularity of formally smooth maps of complete local rings

Source: Stacks Project, More on Algebra, Proposition 07PM, implication (4) to (1)
(blueprint: lem-weil-pbc-formally-smooth-complete-local-regular).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A local map between complete Noetherian local rings, formally smooth for the maximal-ideal
adic topology of the target, is regular. Source: Stacks Project, More on Algebra,
Proposition 07PM, implication (4) to (1).
(blueprint: lem-weil-pbc-formally-smooth-complete-local-regular)

Proof plan:
1. By fs-adic-flat-geometrically-regular-closed-fibre, the map is flat and its closed fibre
   is geometrically regular. Fix a prime p of A; we must establish geometric regularity
   and Noetherianity of its fibre, as in def-weil-pbc-g-ring.
2. Replace A and B by A/p and B/pB using complete-local-quotient and fs-adic-base-change.
   The new base is a complete local domain with fraction field kappa(p). By tensor
   associativity, it suffices to show regularity after each finite purely inseparable
   extension of this fraction field.
3. By complete-local-domain-finite-over-regular, choose a complete regular coefficient
   subring A0, finite in A and with the same residue field. Base change makes the closed
   fibre formally smooth. By fs-adic-lift-over-finite-coefficient-map, lift it to a
   complete Noetherian local A0-algebra C with B isomorphic to C tensor over A0 with A.
4. Localizing A at the nonzero elements of A0 gives its fraction field, finite over the
   fraction field K0 of A0 (localization-base-change). Tensor associativity reduces the
   task to geometric regularity of C tensor over A0 with K0, using
   geometrically-regular-finitely-generated-extensions.
5. By fs-adic-flat-geometrically-regular-closed-fibre and
   flat-over-regular-with-regular-fibre, C is regular. Its localization at K0 is regular
   and Noetherian by localization-of-regular-ring.
6. In characteristic zero there are no nontrivial finite purely inseparable extensions;
   this includes the Cohen-ring coefficient case. Step 5 therefore suffices there.
7. In characteristic p, induct on the degree of a finite purely inseparable extension.
   By purely-inseparable-pth-root-tower the last step adjoins a pth root of f. Clear
   denominators to obtain a finite A0-subalgebra A' of the intermediate field, with that
   field as fraction field, and f in A'.
8. By derivation-nonzero-on-non-pth-power choose a derivation D of A' nonzero on f.
   Base change preserves formal smoothness; finite-module-complete-over-complete-noetherian
   gives completeness of C tensor A'. By fs-adic-lift-derivation extend D to this ring,
   then use derivation-extends to localize. Its value on f is now a unit.
9. By degree-p-extension-regular the pth-root extension of the inductively regular ring
   is regular. Tensor associativity identifies it with the required base change. This
   proves geometric regularity and Noetherianity at every prime; with step 1 the map
   is regular. -/
theorem isRegular_of_formallySmoothAdic
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (φ : A →+* B) [IsLocalHom φ]
    (hfs : letI : Algebra A B := φ.toAlgebra
      Algebra.FormallySmoothAdic A B (IsLocalRing.maximalIdeal B)) :
    φ.IsRegular := by
  sorry

end RingHom
