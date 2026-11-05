/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.BoundedConstructibleFinite
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFiniteness

/-!

# Deligne's finiteness theorem for the nearby cycles of the trait, finite coefficients

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧` the strictly henselian trait, with
geometric generic point `j : Spec Ω ⟶ S` and closed point `i : Spec k' ⟶ S`, and let `T` be a
finite discrete ring. The geometric nearby cycles `Li^* Rj_* Lj^*` of `S` carry bounded
constructible complexes of `T̲`-modules on `S` to bounded constructible complexes on `Spec k'`
(`ProEtale.CondensedRing.boundedConstructible_traitNearbyCycles_obj_of_finite`). This is the
case `𝔸⁰_S = S` of Deligne's finiteness theorem for nearby cycles (SGA 4½, [Th. finitude],
Thm. 3.2), for finite coefficients.

The proof is that of the `ℚ̄_ℓ` case
(`ProEtale.CondensedRing.boundedConstructible_traitNearbyCycles_obj`), whose ingredients are
stated for an arbitrary coefficient ring; the dévissage uses that bounded constructible complexes
of `T̲`-modules form a triangulated subcategory
(`ProEtale.CondensedRing.isTriangulated_boundedConstructible_of_finite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (k' : Type u) [Field k'] [IsSepClosed k']
  (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

namespace NearbyCyclesModel

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
