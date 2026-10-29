/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported

/-!

# Compatibility of the smooth trace with base change

Let `f : X ⟶ Y` be smooth of pure relative dimension `d` and consider a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
of separated `k`-schemes of finite type. The smooth trace `Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace`) is compatible with base change (SGA 4,
Exposé XVIII, Théorème 2.9 (Var 4)): pulled back along `g` and read through compact-support base
change `Lg^* Rf_! ≅ Rf'_! Lg'^*`, it is the trace of `f'`, up to the identification
`Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,X'(d)[2d]` of the Tate twists.

This is a property of the sorried definition `smoothTrace` of `WeilConjectures.SmoothPurity.Defs`,
owed by the smooth purity section (blueprint `sk-prop-sp-purity-bc`), and is stated here,
`sorry`ed, as `AlgebraicGeometry.ProEtale.CondensedRing.exists_iso_smoothTrace_baseChange`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

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
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Blueprint `sk-prop-sp-purity-bc` (owed by the smooth purity section, `sec-smooth-purity`):
**the smooth trace is compatible with base change** (SGA 4, Exposé XVIII, Théorème 2.9
(Var 4)). For a cartesian square with `f` (hence `f'`) smooth of pure relative dimension `d`,
the trace of `f'` is, up to an isomorphism `Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,X'(d)[2d]` of the Tate
twists, the pullback of the trace of `f` read through compact-support base change:
```
Rf'_! Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ Lg^* Rf_! ℚ̄_ℓ,X(d)[2d] --Lg^* Tr_f--> Lg^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,Y'.
```
This is a property of the sorried definition `smoothTrace`. -/
theorem exists_iso_smoothTrace_baseChange (sq : IsPullback g' f' f g) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left] :
    ∃ τ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ≅
          boundedConstructibleTateTwist ℓ X' d (2 * d),
      haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
      (boundedConstructibleLowerShriek ℓ f').map τ.hom ≫ smoothTrace ℓ f' d =
        inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
            (boundedConstructibleTateTwist ℓ X d (2 * d))) ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
            (smoothTrace ℓ f d) ≫
          η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
