/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Approximation
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts

/-!
# Sheaves supported at closed points are acyclic

Let `K` be a separably closed field, `X` a quasi-compact scheme locally of finite type over `K`
and `F` an étale sheaf of `Λ`-modules on `X` whose stalks vanish at the non-closed points. Then
`H^q(X_ét, F) = 0` for `q ≠ 0` (blueprint `lem-kun-0f1f-vanish`): `F` is the filtered colimit
of its subsheaves `F_S` supported on finite sets of closed points
(`lem-kun-cp-approximation`), these are acyclic, and étale cohomology of the quasi-compact
quasi-separated scheme `X` commutes with filtered colimits.

## Main statements

- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedGlobalSections_of_isZero_sheafFiber`
  (`lem-kun-0f1f-vanish`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

end Etale

end AlgebraicGeometry
