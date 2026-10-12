/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction

/-! # Invertibility of the strict-local cohomology comparison

Source: Stacks Project, Tag 03Q9.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The cohomology comparison in the unrestricted stalk formula is invertible.
Source: Stacks Project, Tag 03Q9; this intermediate packages the compatibility of the
strict-local base-change mate, Leray comparison, and exact inverse-image identifications.
(blueprint: lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison).

Proof: apply strict-local base-change on global homology to the single complex F[0].
The displayed comparison is the composite of four maps: global sections of the exact
inverse-image/homology isomorphism; global sections of the homology of the derived
base-change mate; the strict-local Leray homology isomorphism; and cohomology of the
inverse-image/single-complex isomorphism. The second factor is invertible by the
strict-local base-change theorem; the other three are images of isomorphisms under
functors. Thus their composite is invertible. This holds for q = 0 and higher q,
including zero sheaves and empty X, and requires no torsion hypothesis.
-/
theorem isIso_strictHenselizationCohomologyComparison
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) (q : ℕ) :
    IsIso (strictHenselizationCohomologyComparison xbar f F q) := by
  sorry

end AlgebraicGeometry.Etale
