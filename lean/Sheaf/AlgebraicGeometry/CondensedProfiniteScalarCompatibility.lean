/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel

/-! # Scalar associativity for condensed realization on a profinite slice

Source: Hemo--Richarz--Scholbach, Remark 3.2 and formula (3.2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Realization on a profinite slice factors through its actual section ring.
No disconnectedness hypothesis is needed for scalar associativity.

Source: Hemo--Richarz--Scholbach, (3.2) and Remark 3.2; Stacks Tags 06YY and 07A4
(blueprint: lem-zl-condensed-profinite-scalar-compatibility).

Proof: restriction to the slice preserves constant sheaves and identifies the
restriction of the point coefficient map with the composite of the constant
scalar map R to A and the terminal constant-section map to the coefficient
sheaf. The ring isomorphism used here is `profiniteSectionRingIso`; its maps
preserve multiplication and the scalar inclusion by construction. Choose a
flat-term K-flat representative P of an arbitrary unbounded R-complex.
Restriction preserves the required K-flatness, and constants commute with
scalar extension by the constant-realization scalar comparison. Associativity
of ordinary balanced tensor products then gives the map
b tensor (a tensor p) to ba tensor p; its inverse is b tensor p to
b tensor (1 tensor p). The balanced relations prove that they are inverse,
and their formulas commute with differentials and with all chain maps.
Localizing the K-flat representatives gives the asserted natural isomorphism,
including all unbounded complexes. On the empty slice the section ring is zero,
so both sides are zero, as the same formulas require. -/
theorem condensed_profinite_scalar_compatibility
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (S : Profinite.{u}) :
    profiniteScalarClause Λ.X S := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
