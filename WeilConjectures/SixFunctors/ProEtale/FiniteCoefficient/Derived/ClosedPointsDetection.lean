/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Detection
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived

/-!
# Detection of pro-étale complexes supported at closed points

Let `k` be a separably closed field, `X` a scheme locally of finite type over `k` with structure
morphism `p`, and `T` a finite discrete ring. A complex `C` of modules over the condensed
coefficient ring `T̲` on `X_proét` which is bounded below of étale origin vanishes as soon as
its pullbacks to (neighbourhoods of) the non-closed points of `X` vanish and `Rp_* C = 0`
(Stacks 0F1G). Writing the comparison of `C` with pro-étale sheaves of `T`-modules as `ν^* G`
for a bounded below étale complex `G`, this is reduced to the étale statement
`AlgebraicGeometry.Etale.isZero_iff_forall_isZero_homology_rightDerivedGlobalSections_of_isGE`:
the pullbacks of `G` to the geometric points over the non-closed points vanish, and
`RΓ(X_ét, G) = RΓ(Spec k, Rp_* G)` with `Rp_* G ≅ Rν_* Rp_* ν^* G = 0`.

## Main statements

- `AlgebraicGeometry.ProEtale.CondensedRing.isZero_of_isZero_leftDerivedUpperStar_of_not_isClosed`
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed`
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
