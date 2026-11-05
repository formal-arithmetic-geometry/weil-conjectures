/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward

/-!
# Closed pushforward and extension of scalars

Let `Λ` be a commutative condensed ring, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` a
quasi-compact open immersion onto its complement. This file proves, without the bounded
constructible six functor formalism of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` (which depends
on the present file through the descent of constructible complexes), that for a flat coefficient
change `a : Λ ⟶ Λ'` the extension of scalars commutes with `Ri_*`:
`T^X (Ri_* N) ≅ Ri_* (T^Z N)`
(`ProEtale.CondensedRing.derivedExtendScalarsLowerStarIsoOfIsClosedImmersion`). Indeed
`Lj^* T^X (Ri_* N) ≅ T^U (Lj^* Ri_* N) = 0` by (Pull), so `T^X (Ri_* N)` is supported on `Z`
(`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
