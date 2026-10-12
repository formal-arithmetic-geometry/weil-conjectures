/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms

/-! # Canonical derived sections and strict-local cohomology germs

Source: Stacks Project, Tags 03Q8 and 03Q9. The derived Hom comparison is the
explicit free-abelian-sheaf construction used in AbelianHigherDirectImagePresheaf.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The canonical derived-sections comparison induces an isomorphism on geometric stalks.
This is only the local sheafification assertion, with no strict-local limit or base-change mate.
Source: Stacks, Tag 03Q8 and Cohomology on Sites, Tag 0BKV
(blueprint: lem-weil-pbc-derived-cohomology-germ-isomorphism).

Proof: represent L[n] by a bounded below K-injective complex M. The derived Hom from
Z[U][0] is represented by cycles in M(U), modulo boundaries. The displayed map sends
such a cycle to its homology section. Locally, every homology section lifts to a cycle,
because cycles surject onto the homology sheaf. If the homology section of a cycle
vanishes, locally the cycle lifts through the differential from degree -1; the lift is
a null homotopy of the map from Z[U][0]. Hence the comparison is locally bijective.
Sheafification makes it an isomorphism, and geometric stalks are unchanged by
sheafification. Finally the homology shift isomorphism transports H^0(L[n]) to H^n(L).
The cycle and boundary argument applies for every integer n and also for L = 0. -/
theorem isIso_strictLocalCohomologyGermMap {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso ((Scheme.pointSmallEtale s).presheafFiber.map
      (strictLocalCohomologyGermMap L n)) := by sorry

end AlgebraicGeometry.Etale
