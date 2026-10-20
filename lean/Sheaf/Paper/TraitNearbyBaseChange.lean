/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeFilteredColimit
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.OrgogozoGoodModification
import Sheaf.Paper.OrientedNearbyStrictLocalDescription
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Nearby-cycle base change over a trait

Source: Lu--Zheng, *Duality and nearby cycles over general bases*, §4.5,
Example 4.26(2), valuation-ring case, p. 37 of the author PDF
(blueprint: lem-trf-trait-nearby-base-change).

## Main statements

* `trait_nearby_base_change`: every bounded complex of finite torsion coefficients
  on a finite-type scheme over a discrete valuation ring is `Psi`-good.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedNearbyCycles

/--
For a finite-type morphism to the spectrum of a discrete valuation ring, every bounded
complex with finite torsion commutative coefficients satisfies arbitrary base change for
oriented nearby cycles.

Source: Lu--Zheng, *Duality and nearby cycles over general bases*, §4.5,
Example 4.26(2), valuation-ring case, p. 37 of the author PDF
(blueprint: lem-trf-trait-nearby-base-change).

Proof plan. A discrete valuation ring is a local principal ideal domain, hence a
Noetherian integral base; finite type then gives the required quasi-compact,
quasi-separated source. For a constructible coefficient sheaf, the good-modification
 theorem over an integral Noetherian base gives a proper modification that is good.
The generic point of the trait lifts through the modification, and the proper valuative
criterion extends this lift to a section because a local PID is a valuation ring.
The counit definition of the ordinary comparison is compatible with successive base
changes, so goodness descends along this section. Strict-local descriptions of nearby
cycles identify their cohomology with higher direct images between affine strict
local schemes; continuity of higher direct images through filtered colimits proves the
comparison for arbitrary module sheaves. Finally, truncation triangles, shift
compatibility, and induction on the finite cohomological range extend the result to
bounded complexes. The argument uses no flatness, properness, or smoothness of the
finite-type morphism.
-/
theorem trait_nearby_base_change
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (m : ℕ) (hm : 1 ≤ m)
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (hmΛ : ∀ x : Λ, m • x = 0) (hm_unit : IsUnit (m : R))
    (T : Scheme.{u}) (f : T ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : EtaleDerived T Λ)
    (hL : IsBounded (etaleDatum T) (Coeff Λ) L) :
    IsPsiGood f Λ L := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
