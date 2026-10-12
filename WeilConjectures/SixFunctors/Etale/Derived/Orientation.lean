/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!

# Orientations and the dual of a perfect complex

Let `Λ` be a finite coefficient ring carrying a Tate twist datum (`HasTateTwist Λ`), with
twisting objects `Λ_X(d) = tateObject Λ X d`. For a smooth separated morphism `f : X ⟶ Y` of
finite type and of pure relative dimension `d`, *smooth purity* provides a canonical isomorphism
`Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`, that is `Λ_X(d)[2d] ≅ Rf^! Λ_Y`. It is
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift` (`sk-thm-smooth-purity`),
which gives orientations through `AlgebraicGeometry.Etale.Orientation.nonempty`. What is
recorded in this file is the interface it produces, packaged as a structure
`AlgebraicGeometry.Etale.Orientation`, together with the two consequences the six-functor
formalism uses: for the structure morphism `a : X ⟶ S` an orientation reads
`ω_X ≅ Λ_X(d)[2d]`, and substituting that into `𝔻_X = RHom(-, ω_X)` turns the Verdier dual of a
perfect complex into its coefficient dual, twisted and shifted.

## Main definitions

- `AlgebraicGeometry.Etale.Orientation`: the interface record of an orientation of relative
  dimension `d`, namely the smoothness of `f` together with `Λ_X(d)[2d] ≅ Rf^! Λ_Y` for the
  Tate twist `Λ_X(d)`.
- `AlgebraicGeometry.Etale.Orientation.ofDualizingComplexIso`: the orientation given by an
  isomorphism `Λ_X(d)[2d] ≅ ω_X` for a smooth `a` of relative dimension `d`.
- `AlgebraicGeometry.Etale.Orientation.twistShiftIso` (`rem-ptr-sf-orientation-2`): the purity
  isomorphism in the twist conventions of `def-coefficient-twists-detailed`,
  `(twistShift Λ X d).obj Λ_X ≅ Rf^! Λ_Y`.

## Main statements

- `AlgebraicGeometry.Etale.Orientation.nonempty` (`rem-sf-orientation-pointer`): orientations
  are not assumed; smooth purity constructs one for every smooth separated `f` of pure relative
  dimension `d` over a separated scheme locally of finite type over a field.
- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`
  (`sk-def-sf-orientation`): for the structure morphism the orientation reads
  `ω_X ≅ Λ_X(d)[2d]`.
- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual`
  (`sk-thm-sf-dual-perfect`): `𝔻_X K ≅ K^∨(d)[2d]` for a perfect `K`.
- `AlgebraicGeometry.Etale.Orientation.isDualizable_verdierDual`
  (`sk-thm-sf-dual-perfect`): `𝔻_X` preserves the perfect objects.

## Implementation notes

The twist of an orientation is *the* Tate twist `tateObject Λ X d` of the Tate twist datum,
not an arbitrary invertible object: an arbitrary invertible `T` with `T[2d] ≅ Rf^! Λ_Y` exists
for every `d` as soon as `Rf^! Λ_Y` is invertible (take `T = Rf^! Λ_Y [-2d]`), so it would record
neither `d` nor the twist. The unit `Lf^* Λ_Y ≅ Λ_X` is left out of the purity isomorphism: it
is always invertible, and leaving it out keeps the field free of the comparison between `⊗` and
`AlgebraicGeometry.Etale.derivedTensor`. Likewise `f` is required to be smooth of relative
dimension `d`. Constructions that only use the shape of the purity isomorphism, such as the
derived Poincaré pairing of `WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing`, take
an isomorphism `T⟦2d⟧ ≅ ω_X` as an argument instead.

Perfectness is `CategoryTheory.IsDualizable`; see the implementation note of
`WeilConjectures.SixFunctors.Etale.Derived.Perfect`.


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
`γ : Λ_X(d)[2d] ≅ Rf^! Λ_Y`, where `Λ_X(d) = tateObject Λ X d` is the Tate twist. Since
`Lf^* Λ_Y ≅ Λ_X` (`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_unit`), this is the
blueprint's `Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`.

In the blueprint an orientation is **not** an assumption: it is the smooth purity theorem
`sk-thm-smooth-purity`, which lives in a different blueprint block; see
`AlgebraicGeometry.Etale.Orientation.nonempty` (`rem-sf-orientation-pointer`).
This structure therefore records only the interface that purity produces and that the six
operations consume. The blueprint's naturality in `Y` and its compatibilities with composition,
étale base change, finite reduction, scalar extension and the pro-étale realization concern the
whole family of orientations; they are the conditions of
`AlgebraicGeometry.Etale.OrientationDatum` (`def-sf-orientation`).

For the structure morphism `f = a_X` the isomorphism reads `ω_X ≅ Λ_X(d)[2d]`; see
`AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`. -/
structure Orientation (f : X ⟶ Y) (d : ℕ) [HasCompactification f] where
  /-- The morphism is smooth of pure relative dimension `d`. -/
  smoothOfRelativeDimension : SmoothOfRelativeDimension d f
  /-- The purity isomorphism `γ : Λ_X(d)[2d] ≅ Rf^! Λ_Y`. -/
  purity : (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) f

variable {Λ}

/-- The twist `Λ_X(d)` of an orientation of relative dimension `d`: the Tate twist
`tateObject Λ X d`. -/
noncomputable abbrev Orientation.twist {f : X ⟶ Y} {d : ℕ} [HasCompactification f]
    (_o : Orientation Λ f d) : DerivedCategoryModule Λ X :=
  tateObject Λ X d

/-- Blueprint `rem-ptr-sf-orientation-2`: Pointer to the properties of [def-sf-orientation].

The purity isomorphism of an orientation, read in the Tate twist conventions of
`def-coefficient-twists-detailed`: the source `Λ_X(d)[2d]` is the twist-and-shift
`(twistShift Λ X d).obj Λ_X = (Λ_X ⊗ Λ_X(d))[2d]` of the constant complex, so that `γ` takes
the form in which smooth purity
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`) states it. -/
noncomputable def Orientation.twistShiftIso {f : X ⟶ Y} {d : ℕ} [HasCompactification f]
    (o : Orientation Λ f d) :
    (twistShift Λ X d).obj (constantComplex Λ X) ≅ dualizingComplex (ModuleCat.{u + 1} Λ) f :=
  twistShiftConstantComplexIso Λ X d ≪≫ o.purity

/-- Blueprint `rem-sf-orientation-pointer`: Where the orientation is constructed.

The orientation datum is not an assumption: for `f : X ⟶ Y` smooth separated of pure relative
dimension `d`, with `Y` separated and locally of finite type over a field `k` and the exponent
of `Λ` invertible on `X`, smooth purity (`sk-thm-smooth-purity`,
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`) gives
`Rf^! Λ_Y ≅ Λ_X(d)[2d]`, hence an orientation of `f` of relative dimension `d`. -/
theorem Orientation.nonempty [HasTateTwist.IsNormalized Λ] {d : ℕ} (f : X ⟶ Y)
    [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
    [HasInvertibleExponent Λ X] {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] :
    Nonempty (Orientation Λ f d) := by
  obtain ⟨e⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) f aY
  exact ⟨⟨inferInstance, (twistShiftConstantComplexIso Λ X d).symm ≪≫ e.symm⟩⟩

variable {S : Scheme.{u}} {d : ℕ} {a : X ⟶ S} [HasCompactification a]

/-- The orientation of a structure morphism `a : X ⟶ S`, smooth of relative dimension `d`,
given by an isomorphism `γ : Λ_X(d)⟦2d⟧ ≅ ω_X`. This is how an orientation in the form
`Λ_X(d)[2d] ≅ ω_X`, as produced by smooth purity
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), is turned into an
`AlgebraicGeometry.Etale.Orientation`. -/
def Orientation.ofDualizingComplexIso [SmoothOfRelativeDimension d a]
    (γ : (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a) :
    Orientation Λ a d where
  smoothOfRelativeDimension := inferInstance
  purity := γ

/-- Blueprint `sk-def-sf-orientation`: Orientation: an interface record.

The special case of the orientation at the structure morphism `a : X ⟶ S`: `Ra^! Λ_S` is by
definition the dualizing complex, so the purity isomorphism reads
```
ω_X ═══ Ra^! Λ_S ≅ Λ_X(d)[2d]
```
the dualizing complex of a smooth `X` of pure relative dimension `d` over `S` is a shifted Tate
twist. -/
theorem Orientation.nonempty_iso_dualizingComplex (o : Orientation Λ a d) :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) a ≅ (tateObject Λ X d)⟦(2 * d : ℤ)⟧) :=
  ⟨o.purity.symm⟩

/-- Blueprint `sk-thm-sf-dual-perfect`: The dual of a perfect complex.

Let `a : X ⟶ S` be a structure morphism admitting a compactification, let `o` be an
orientation of `a` of relative dimension `d`, and let `K` be perfect over `Λ_X`, i.e.
dualizable. Substituting `ω_X ≅ Λ_X(d)[2d]` into `𝔻_X K = RHom_X(K, ω_X)` and interchanging
the twist with the internal hom identifies the Verdier dual of `K` with the twisted, shifted
coefficient dual: `𝔻_X K ≅ K^∨(d)[2d]`. -/
theorem Orientation.nonempty_iso_verdierDual_coefficientDual (o : Orientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : IsDualizable K) :
    Nonempty ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))).obj
          ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)) := by
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_derivedHom_derivedTensor hK
    ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)
  exact ⟨(RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).mapIso o.purity.symm ≪≫ e⟩

/-- Blueprint `sk-thm-sf-dual-perfect`: The dual of a perfect complex.

Under an orientation the Verdier dual of a perfect complex is perfect, so that `𝔻_X`
restricts to a contravariant anti-equivalence of the perfect objects. -/
theorem Orientation.isDualizable_verdierDual [HasInvertibleExponent Λ X] (o : Orientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : IsDualizable K) :
    IsDualizable ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)) := by
  obtain ⟨e⟩ := o.nonempty_iso_verdierDual_coefficientDual hK
  have hT : IsInvertible (tateObject Λ X d) :=
    (isInvertible_iff_exists_derivedTensor _).2 (isInvertible_tateObject Λ X d)
  exact IsDualizable.of_iso e.symm (DerivedCategory.isDualizable_derivedTensor
    (DerivedCategory.isDualizable_coefficientDual hK)
    (DerivedCategory.isDualizable_of_isInvertible (DerivedCategory.isInvertible_shift hT _)))

end Etale

end AlgebraicGeometry
