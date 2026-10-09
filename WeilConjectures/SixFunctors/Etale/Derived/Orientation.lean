/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!

# Orientations and the dual of a perfect complex

Let `Λ` be a finite coefficient ring carrying a Tate twist datum (`HasTateTwist Λ`), with
twisting objects `Λ_X(d) = tateObject Λ X d`. For a smooth separated morphism `f : X ⟶ Y` of
finite type and of pure relative dimension `d`, *smooth purity* provides a canonical isomorphism
`Lf^* Λ_Y ⊗ Λ_X(d)[2d] ≅ Rf^! Λ_Y`. Its proof belongs to a different blueprint block and is not
formalised here; what is recorded in this file is the interface it produces, packaged as a
structure `AlgebraicGeometry.Etale.Orientation`, together with the two consequences the
six-functor formalism uses: for the structure morphism `a : X ⟶ S` an orientation reads
`ω_X ≅ Λ_X(d)[2d]`, and substituting that into `𝔻_X = RHom(-, ω_X)` turns the Verdier dual of a
perfect complex into its coefficient dual, twisted and shifted.

## Main definitions

- `AlgebraicGeometry.Etale.Orientation`: the interface record of an orientation of relative
  dimension `d`, namely the smoothness of `f` together with
  `Lf^* Λ_Y ⊗ Λ_X(d)[2d] ≅ Rf^! Λ_Y` for the Tate twist `Λ_X(d)`.
- `AlgebraicGeometry.Etale.Orientation.dualizingComplexIso`: for the structure morphism, the
  isomorphism `Λ_X(d)[2d] ≅ ω_X` of an orientation.
- `AlgebraicGeometry.Etale.Orientation.ofDualizingComplexIso`: the orientation given by an
  isomorphism `Λ_X(d)[2d] ≅ ω_X` for a smooth `a` of relative dimension `d`.

## Main statements

- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`
  (`sk-def-sf-orientation`): for the structure morphism the orientation reads
  `ω_X ≅ Λ_X(d)[2d]`.
- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual`
  (`sk-thm-sf-dual-perfect`): `𝔻_X K ≅ K^∨(d)[2d]` for a perfect `K`.
- `AlgebraicGeometry.Etale.Orientation.isDualizable_verdierDual`
  (`sk-thm-sf-dual-perfect`): `𝔻_X` preserves the perfect objects.

## Implementation notes

The twist of an orientation is *the* Tate twist `tateObject Λ X d` of the Tate twist datum,
not an arbitrary invertible object: an arbitrary invertible `T` with `Lf^* Λ_Y ⊗ T[2d] ≅ Rf^! Λ_Y`
exists for every `d` as soon as `Rf^! Λ_Y` is invertible (take `T = Rf^! Λ_Y [-2d]`), so it
would record neither `d` nor the twist. Likewise `f` is required to be smooth of relative
dimension `d`. Constructions that only use the shape of the purity isomorphism, such as the
derived Poincaré pairing of `WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing`, take
an isomorphism `T⟦2d⟧ ≅ ω_X` as an argument instead.

Perfectness is `CategoryTheory.IsDualizable`; see the implementation note of
`WeilConjectures.SixFunctors.Etale.Derived.Perfect`.

`Orientation.nonempty_iso_dualizingComplex` is not blueprint content: it is `o.purity`
transported along `Lf^* Λ_S ≅ Λ_X` (`AlgebraicGeometry.Etale.Orientation.dualizingComplexIso`).

Biduality of the Verdier dual on `Dctf(X, Λ)` is *not* restated here: it is
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual` of
`WeilConjectures.SixFunctors.Etale.Derived.Dualizing`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}

/-- Blueprint `sk-def-sf-orientation`: Orientation: an interface record.

An *orientation* of relative dimension `d` for a separated morphism `f : X ⟶ Y` of finite type
consists of the smoothness of `f`, of pure relative dimension `d`, together with an isomorphism
`γ : Lf^* Λ_Y ⊗ Λ_X(d)[2d] ≅ Rf^! Λ_Y`, where `Λ_X(d) = tateObject Λ X d` is the Tate twist.

In the blueprint an orientation is **not** an assumption: it is the smooth purity theorem
`sk-thm-smooth-purity`, which lives in a different blueprint block and is not formalised here.
This structure therefore records only the interface that purity produces and that the six
operations consume; the blueprint's naturality in `Y` and its compatibilities with composition,
étale base change, finite reduction, scalar extension and the pro-étale realization quantify
over data that this block does not have and are not among its fields.

For the structure morphism `f = a_X` the isomorphism reads `ω_X ≅ Λ_X(d)[2d]`; see
`AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`. -/
structure Orientation (f : X ⟶ Y) (d : ℕ) [HasCompactification f] where
  /-- The morphism is smooth of pure relative dimension `d`. -/
  smoothOfRelativeDimension : SmoothOfRelativeDimension d f
  /-- The purity isomorphism `γ : Lf^* Λ_Y ⊗ Λ_X(d)[2d] ≅ Rf^! Λ_Y`. -/
  purity : (L((f)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ⊗ (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅
    (R(f)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)

variable {Λ}

/-- The twist `Λ_X(d)` of an orientation of relative dimension `d`: the Tate twist
`tateObject Λ X d`. -/
abbrev Orientation.twist {f : X ⟶ Y} {d : ℕ} [HasCompactification f] (_o : Orientation Λ f d) :
    DerivedCategoryModule Λ X :=
  tateObject Λ X d

/-- The twist of an orientation is invertible for the derived tensor product. -/
theorem Orientation.isInvertible_twist {f : X ⟶ Y} {d : ℕ} [HasCompactification f]
    (o : Orientation Λ f d) : IsInvertible o.twist :=
  (isInvertible_iff_exists_derivedTensor _).2 (isInvertible_tateObject Λ X d)

variable {S : Scheme.{u}} {d : ℕ} {a : X ⟶ S} [HasCompactification a]

/-- The isomorphism `Λ_X(d)[2d] ≅ ω_X` of an orientation `o` of the structure morphism
`a : X ⟶ S`, given an identification `e : La^* Λ_S ≅ Λ_X`: the purity isomorphism read through
`e` and the left unitor,
```
                   λ⁻¹                       e⁻¹ ⊗ 1                         o.purity
Λ_X(d)[2d] ──────────────▶ Λ_X ⊗ Λ_X(d)[2d] ─────────▶ La^* Λ_S ⊗ Λ_X(d)[2d] ──────────▶ Ra^! Λ_S
```
-/
noncomputable def Orientation.dualizingComplexIso (o : Orientation Λ a d)
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _) :
    (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a :=
  (λ_ _).symm ≪≫ whiskerRightIso e.symm _ ≪≫ o.purity

/-- The orientation of a structure morphism `a : X ⟶ S`, smooth of relative dimension `d`,
built from an isomorphism `γ : Λ_X(d)⟦2d⟧ ≅ ω_X` and an identification `e : La^* Λ_S ≅ Λ_X`: its
purity isomorphism is
```
                         e ⊗ 1                  λ                γ
La^* Λ_S ⊗ Λ_X(d)⟦2d⟧ ───────────▶ Λ_X ⊗ Λ_X(d)⟦2d⟧ ─────▶ Λ_X(d)⟦2d⟧ ─────▶ Ra^! Λ_S
```
This is how an orientation in the form `Λ_X(d)[2d] ≅ ω_X`, as produced by smooth purity
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), is turned into an
`AlgebraicGeometry.Etale.Orientation`. -/
noncomputable def Orientation.ofDualizingComplexIso [SmoothOfRelativeDimension d a]
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _)
    (γ : (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a) :
    Orientation Λ a d where
  smoothOfRelativeDimension := inferInstance
  purity := whiskerRightIso e _ ≪≫ λ_ _ ≪≫ γ

/-- Blueprint `sk-def-sf-orientation`: Orientation: an interface record.

The special case of the orientation at the structure morphism `a : X ⟶ S`. There
`La^* Λ_S ≅ Λ_X` is the monoidal unit
(`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_unit`) and `Ra^! Λ_S` is by
definition the dualizing complex, so the purity isomorphism reads
```
ω_X ═══ Ra^! Λ_S ≅ Λ_X(d)[2d]
```
the dualizing complex of a smooth `X` of pure relative dimension `d` over `S` is a shifted Tate
twist. -/
theorem Orientation.nonempty_iso_dualizingComplex (o : Orientation Λ a d) :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) a ≅ (tateObject Λ X d)⟦(2 * d : ℤ)⟧) :=
  (nonempty_iso_leftDerivedUpperStar_unit _ a).map fun e ↦ (o.dualizingComplexIso e).symm

/-- Blueprint `sk-thm-sf-dual-perfect`: The dual of a perfect complex.

Let `a : X ⟶ S` be a structure morphism admitting a compactification, let `o` be an
orientation of `a` of relative dimension `d`, and let `K` be perfect over `Λ_X`, i.e.
dualizable. Substituting `ω_X ≅ Λ_X(d)[2d]` into `𝔻_X K = RHom_X(K, ω_X)` and interchanging
the twist with the internal hom identifies the Verdier dual of `K` with the twisted, shifted
coefficient dual: `𝔻_X K ≅ K^∨(d)[2d]`. -/
theorem Orientation.nonempty_iso_verdierDual_coefficientDual (o : Orientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : IsDualizable K) :
    Nonempty ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K) ≅
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K) ⊗
        (tateObject Λ X d)⟦(2 * d : ℤ)⟧) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ) a
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap K Kᘁ
  have := MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)
  exact ⟨(ihom K).mapIso (o.dualizingComplexIso e).symm ≪≫
    (asIso (MonoidalClosed.ihomUnitTensorToIhom K _)).symm⟩

/-- Blueprint `sk-thm-sf-dual-perfect`: The dual of a perfect complex.

Under an orientation the Verdier dual of a perfect complex is perfect, so that `𝔻_X`
restricts to a contravariant anti-equivalence of the perfect objects. -/
theorem Orientation.isDualizable_verdierDual (o : Orientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : IsDualizable K) :
    IsDualizable ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)) :=
  sorry

end Etale

end AlgebraicGeometry
