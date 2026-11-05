/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedPointsDetection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin

/-!
# Deligne's finiteness criterion at closed points, pro-étale form

Let `k` be a separably closed field, `p : X ⟶ Spec k` proper, `T` a finite discrete ring whose
exponent is invertible in `k`, and `hᵢ : Wᵢ ⟶ X` finitely many morphisms from Noetherian schemes
whose images contain the non-closed points of `X`. A complex `C` of modules over the condensed
coefficient ring `T̲` on `X_proét` which is bounded below of étale origin is bounded constructible
as soon as its pullbacks `Lhᵢ^* C` and its direct image `Rp_* C` are
(`boundedConstructible_of_leftDerivedUpperStar_of_rightDerivedLowerStar_of_isProper`).

Writing `Φ C ≅ ν^* G` for a bounded below étale complex `G`, this is the étale criterion
`AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar_of_isProper`:
`ν^*` is fully faithful on `D⁺`
(`AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app`)
and commutes with `Lhᵢ^*`, and `Rp_* G ≅ Rν_* Rp_* ν^* G`, so the bounded constructibility of the
pro-étale complexes `Lhᵢ^* C` and `Rp_* C`, which are of étale origin
(`AlgebraicGeometry.ProEtale.isEtaleOrigin_of_isConstructible`), is that of `Lhᵢ^* G` and
`Rp_* G`; conversely `C ≅ Φ⁻¹ ν^* G` is bounded constructible if `G` is
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_inverse_obj_of_etale`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

end AlgebraicGeometry.ProEtale.CondensedRing
