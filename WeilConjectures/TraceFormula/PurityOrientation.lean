/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PurityTensorMap

/-!

# The relative dualizing complex of a smooth morphism

For a smooth morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, the *relative
dualizing complex* `ω_f = Rf^! ℚ̄_ℓ` on `X` is the object through which smooth purity is
expressed: `Rf^! K ≅ Lf^* K ⊗ ω_f` (`ProEtale.CondensedRing.upperShriekUnitTensorMap`). This file
records the two properties of `ω_f` (its *orientation*, blueprint `sk-prop-sp-orientation`,
`sk-prop-cohsm`) which the proof of smooth purity for `ℚ̄_ℓ`-coefficients takes as input:

- `ProEtale.CondensedRing.isDualizable_upperShriek_unit_of_smooth`: `ω_f` is dualizable;
- `ProEtale.CondensedRing.isIso_upperShriekBaseChange_unit_of_smooth`: the formation of `ω_f`
  commutes with base change.

Both are consequences of the trace isomorphism `ω_f ≅ ℚ̄_ℓ(d)[2d]` of a morphism smooth of pure
relative dimension `d` (`ProEtale.CondensedRing.isIso_smoothPurityMap`, built from the smooth trace
`ProEtale.CondensedRing.smoothTrace` of `WeilConjectures.SmoothPurity.Defs`), of the invertibility
of the Tate twists `ℚ̄_ℓ(d)` (blueprint `sk-def-sp-tate-twist`: "each `Λ_X(1)` is locally free of
rank one") and of the compatibility of the smooth trace with base change (SGA 4, Exposé XVIII,
Théorème 2.9 (Var 4)). Neither the smooth trace nor the comparison isomorphisms of Tate twists
along pullbacks are available (see the module docstring of `WeilConjectures.SmoothPurity.Defs`
and of `WeilConjectures.TateTwist.ProEtale`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- **The relative dualizing complex of a smooth morphism is dualizable** (blueprint
`sk-prop-sp-orientation`, `sk-prop-cohsm`: "`ω_f` is pro-étale locally isomorphic to
`Λ_X(d)[2d]`"): for `f` smooth, `Rf^! ℚ̄_ℓ` is a dualizable object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. On the open
and closed subscheme where `f` has relative dimension `d` it is `ℚ̄_ℓ(d)[2d]` by the trace
(`isIso_smoothPurityMap`), and the Tate twist `ℚ̄_ℓ(d)` is invertible. -/
theorem isDualizable_upperShriek_unit_of_smooth (f : X ⟶ Y) [Smooth f.left] :
    IsDualizable ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :=
  sorry

/-- **The formation of the relative dualizing complex of a smooth morphism commutes with base
change** (blueprint `sk-prop-cohsm`, (G12) at the unit: "it identifies `g'^* ω_f` with `ω_{f'}`";
`det-sp-purity-bc-factors` (1); SGA 4, Exposé XVIII, Théorème 2.9 (Var 4), the compatibility of
the smooth trace with base change): for a cartesian square with `f` smooth, the exceptional base
change map at the unit `Lg'^* Rf^! ℚ̄_ℓ ⟶ Rf'^! Lg^* ℚ̄_ℓ` is an isomorphism. -/
theorem isIso_upperShriekBaseChange_unit_of_smooth {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [Smooth f.left] :
    IsIso (upperShriekBaseChange ℓ sq (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
