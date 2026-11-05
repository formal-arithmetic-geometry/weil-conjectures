/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFinitenessFinite
public import WeilConjectures.TraceFormula.Specialization.TraitModelEmbedding
public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchangeFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedPointsFiniteness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStarProperBoundedConstructible

/-!

# The global step of Deligne's finiteness theorem, finite coefficients

Let `S = Spec k'⟦t⟧` with `k'` separably closed, `T` a finite discrete ring whose exponent is
invertible in `k'`, and `q : P ⟶ S` proper, with special fibre `p : P_s ⟶ Spec k'`. For a
bounded constructible complex `B` of `T̲`-modules on `P`:

* the cohomology `Rp_* Ψ_P B` of the geometric nearby cycles of the standard model of `P` is
  bounded constructible
  (`boundedConstructible_lowerStar_nearbyCycles_traitStdModel_of_isProper_of_finite`):
  by the proper exchange
  (`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient`)
  it is `Ψ_S (Rq_* B)`, where `Rq_* B` is bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj_of_isProper_of_finite`)
  and so are the nearby cycles of the trait
  (`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel_of_finite`);
* hence `Ψ_P B` is bounded constructible as soon as its pullbacks along finitely many morphisms
  `hᵢ : Wᵢ ⟶ P_s` from Noetherian schemes, whose images contain the non-closed points, are
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_finite`), by Deligne's
  criterion at closed points
  (`boundedConstructible_of_leftDerivedUpperStar_of_rightDerivedLowerStar_of_isProper`).

This is the global step of Deligne's proof (SGA 4½, [Th. finitude], proof of 3.2).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

variable {k' : Type u} [Field k'] [IsSepClosed k']
  [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k'))]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
