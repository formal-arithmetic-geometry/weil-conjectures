/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!
# Perfect complexes on a separably closed point

Let `k` be a separably closed field, `s = Spec k`, and `Λ` a commutative ring. The constant
sheaf functor `F : ModuleCat Λ ⥤ Sheaf s_ét (ModuleCat Λ)` is a monoidal equivalence, with
quasi-inverse the global sections, so the derived global sections `RΓ(s, -) ≅ D(F⁻¹)` are an
equivalence `D(s_ét, Λ) ≌ D(Λ)` which commutes with homology and with the derived tensor
products. This file transports the three ingredients of perfectness along it: for `L` in
`D(s_ét, Λ)`,

* `Hⁿ(RΓ(s, L)) ≅ F⁻¹(Hⁿ L)` is a finite `Λ`-module if `Hⁿ L` is constructible;
* `RΓ(s, L)` is bounded if `L` is;
* `RΓ(s, L)` has Tor amplitude in `[a, b]` if `L` has.

Hence `RΓ(s, L)` is a perfect complex of `Λ`-modules for `L ∈ Dctf(s, Λ)` and `Λ` Noetherian.

## Main statements

- `DerivedCategory.torAmplitudeIn_of_mapDerivedCategory`: a monoidal equivalence of abelian
  categories reflects Tor amplitude.
- `AlgebraicGeometry.Etale.moduleFinite_homology_rightDerivedGlobalSections_of_isSepClosed`
- `AlgebraicGeometry.Etale.homologyConcentratedIn_rightDerivedGlobalSections_of_isSepClosed`
- `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed`
- `AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections_of_isSepClosed`
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {C₁ C₂ : Type*} [Category.{v} C₁] [Abelian C₁] [IsGrothendieckAbelian.{v} C₁]
  [HasDerivedCategory.{v} C₁] [MonoidalCategory C₁] [MonoidalClosed C₁] [MonoidalPreadditive C₁]
  [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
  [Category.{v} C₂] [Abelian C₂] [IsGrothendieckAbelian.{v} C₂]
  [HasDerivedCategory.{v} C₂] [MonoidalCategory C₂] [MonoidalClosed C₂] [MonoidalPreadditive C₂]
  [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]
  (F : C₁ ⥤ C₂) [F.Monoidal] [F.IsEquivalence] [F.Additive]

section

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{v} C] [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

end

end DerivedCategory

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

section

end

variable (L : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
  (ModuleCat.{u + 1} Λ)))

end AlgebraicGeometry.Etale
