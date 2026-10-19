/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure
public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound
import Sheaf.Paper.AmbientIndDerivedSums
import Sheaf.Paper.AmbientIndDerivedTriangulated
import Sheaf.Paper.IntegralConstructibleCompactness
import Sheaf.Paper.IntegralProperDirectSums
import Sheaf.Paper.ProperHeartBound
import Sheaf.Paper.ProperIndConstructibleUnbounded

/-! # Uniform upper bound for the discarded lower tail

Source: blueprint `sk-lem-proper-unbounded-window` and
`det-prop-int-compactness-direct-sums` (1)-(2).
(blueprint: lem-sfb-adic-proper-truncation-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k hΛ

/-- The direct image of a sufficiently low lower tail has no cohomology in
degree `q` or above, uniformly on the bounded constructible localizing hull.

Source: blueprint `sk-lem-proper-unbounded-window` (arbitrary-complex clause)
and `det-prop-int-compactness-direct-sums` (1)-(2).
(blueprint: lem-sfb-adic-proper-truncation-bound)

Proof: the schemes and their locally closed strata are Noetherian. The class
of complexes with ind-constructible cohomology is replete, triangulated and
closed under ambient sums, and contains every bounded constructible complex.
The universal property of the localizing hull therefore puts K in this class.
For integral coefficients use the same statement for the integral
ind-constructible heart, proved from the local torsion charts and locally free
resolutions; all colimits remain those of ordinary module sheaves.
Choose a uniform geometric fibre-dimension bound d for g. Proper
finiteness bounds the cohomology of direct images of constructible heart
objects in [0,2d+1]. In the integral case the local torsion charts and free
resolutions put derived torsion reductions in degrees [-1,0]. Their proper
direct images vanish above 2d. Use the Milnor sequence for their
countable derived inverse limit. In the rational cases use the proper heart
bound, and for Qlbar descend to finite coefficient subextensions. Bounded-below
filtered continuity extends the bound to the ind-constructible heart. Finite
truncation triangles then bound the image of a bounded-below ind-constructible
complex with cohomology at most b by b+2d+1. Left completeness reconstructs an
arbitrary complex from its lower truncations. The discarded heart layer between
successive lower truncations has image
bounded above by 2d-n. For a fixed degree r choose n at least
max(0,2d-r+2). Both degree-r and degree-(r-1) towers then have invertible
transitions, so their first derived inverse limits vanish. Above b+2d+1 the
degree-r terms also vanish. The Milnor exact sequence gives
the same upper bound without boundedness below. Apply this to
the lower tail in the triangle τ<q-c K → K → τ≥q-c K, with c=2d+1.
Its image is supported in degrees at most q-1, which is the asserted bound.
The constant c is independent of K
and q, including zero complexes and empty fibres.
-/
theorem ellAdic_proper_lowerTail_bound :
    ∃ c : ℕ, ∀ (q : ℤ)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
        (condensedRingObj Λ Z.left))),
      boundedConstructibleLocalizingClosure Λ Z.left K →
      ((R((g.left)_*⟦Λ⟧)).obj
        ((DerivedCategory.TStructure.t.truncLT (q - (c : ℤ))).obj K)).IsLE (q - 1) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
