/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs

/-!
# The proper direct image restricts to the localizing categories, `ℓ`-adic coefficients

Blueprint `proposition-proper-direct-image-extension-zero--1`: for a proper `p : X ⟶ Y`, the
direct image `Rp_*` (exact, being a triangulated functor of the ambient derived categories)
restricts to a functor `Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))`, i.e. maps `Loc(Dctf(X, Λ))` into
`Loc(Dctf(Y, Λ))`. For the `ℓ`-adic coefficient rings `Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` (for which
`Dctf = Dbc`) this is the first half of the statements of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs`; in the namespace
`AlgebraicGeometry.ProEtale.CondensedRing`:

* `localizingBoundedConstructible_rightDerivedLowerStar_padicIntegers`;
* `localizingBoundedConstructible_rightDerivedLowerStar_continuousMap`;
* `localizingBoundedConstructible_rightDerivedLowerStar_padicAlgCl`.

For finite coefficient rings, see
`AlgebraicGeometry.ProEtale.DerivedCategory.localizingConstructibleFiniteTor_rightDerivedLowerStar`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

include ℓ k

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- Blueprint `proposition-proper-direct-image-extension-zero--1`: Proper direct image on the
localizing categories, for `Λ = 𝒪̲_E` (for which `Dctf = Dbc`). For a proper `p : X ⟶ Y` of
separated finite-type `k`-schemes, `Rp_*` (exact, being triangulated) restricts to a functor
`Loc(Dbc(X, 𝒪_E)) ⥤ Loc(Dbc(Y, 𝒪_E))`: it maps `Loc(Dbc(X, 𝒪_E))` into `Loc(Dbc(Y, 𝒪_E))`. -/
theorem localizingBoundedConstructible_rightDerivedLowerStar_padicIntegers (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] (p : X ⟶ Y) [IsProper p.left]
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)))
    (hM : localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left M) :
    localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y.left
      ((R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj M) :=
  (localizingBoundedConstructible_rightDerivedLowerStar_padicIntegersRingObj ℓ E p).1 M hM

/-- Blueprint `proposition-proper-direct-image-extension-zero--1`: Proper direct image on the
localizing categories, for `Λ = E̲` (for which `Dctf = Dbc`), `E` a finite extension of `ℚ_ℓ` in
`ℚ̄_ℓ`. For a proper `p : X ⟶ Y` of separated finite-type `k`-schemes, `Rp_*` (exact, being
triangulated) restricts to a functor `Loc(Dbc(X, E)) ⥤ Loc(Dbc(Y, E))`: it maps
`Loc(Dbc(X, E))` into `Loc(Dbc(Y, E))`. -/
theorem localizingBoundedConstructible_rightDerivedLowerStar_continuousMap
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (p : X ⟶ Y) [IsProper p.left]
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X.left)))
    (hM : localizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X.left M) :
    localizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y.left
      ((R((p.left)_*⟦Profinite.continuousMapRingObj.{u} E⟧)).obj M) :=
  ((localizingBoundedConstructible_lowerStar_lowerShriek_continuousMapRingObj ℓ E
    (X' := X)).1 p).1 M hM

/-- Blueprint `proposition-proper-direct-image-extension-zero--1`: Proper direct image on the
localizing categories, for `Λ = ℚ̲̄_ℓ` (for which `Dctf = Dbc`). For a proper `p : X ⟶ Y` of
separated finite-type `k`-schemes, `Rp_*` (exact, being triangulated) restricts to a functor
`Loc(Dbc(X, ℚ̄_ℓ)) ⥤ Loc(Dbc(Y, ℚ̄_ℓ))`: it maps `Loc(Dbc(X, ℚ̄_ℓ))` into
`Loc(Dbc(Y, ℚ̄_ℓ))`. -/
theorem localizingBoundedConstructible_rightDerivedLowerStar_padicAlgCl (p : X ⟶ Y)
    [IsProper p.left]
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X.left)))
    (hM : localizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X.left M) :
    localizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y.left
      ((R((p.left)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧)).obj M) :=
  ((localizingBoundedConstructible_lowerStar_lowerShriek_padicAlgClRingObj ℓ
    (X' := X)).1 p).1 M hM

end AlgebraicGeometry.ProEtale.CondensedRing
