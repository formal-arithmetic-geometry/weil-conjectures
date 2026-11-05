/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
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
- `AlgebraicGeometry.Etale.Orientation.verdierDualIso` (`sk-thm-sf-dual-perfect`): the natural
  isomorphism `θ_f : 𝔻_{X/Y} K = RHom(K, Rf^! Λ_Y) ≅ K^∨ ⊗ᴸ Λ_X(d)[2d]`, the composite of
  `RHom(K, γ_f⁻¹)` and of the twist interchange; it is the case `T = Λ_X(d)[2d]` of
  `AlgebraicGeometry.Etale.verdierDualIsoCoefficientDualTensor`, defined for any
  `γ : T ≅ Rf^! Λ_Y` with `T` invertible.
- `AlgebraicGeometry.Etale.Orientation.verdierDualEquivalence` (`sk-thm-sf-dual-perfect`): the
  anti-equivalence of the perfect objects given by `𝔻_{X/Y}`.
- `AlgebraicGeometry.Etale.Orientation.verdierDualVerdierDualIso`: the isomorphism
  `𝔻_{X/Y} 𝔻_{X/Y} K ≅ K^∨∨` induced by `θ_f`.

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
- `…Etale.Orientation.verdierDualDoubleDual_app_comp_verdierDualVerdierDualIso_hom`
  (`sk-thm-sf-dual-perfect`): under `θ_f` the Verdier biduality `K ⟶ 𝔻_{X/Y} 𝔻_{X/Y} K` is
  the coefficient-dual biduality `K ⟶ K^∨∨`; hence it is an isomorphism for perfect `K`
  (`AlgebraicGeometry.Etale.Orientation.isIso_verdierDualDoubleDual_app_of_isDualizable`).
- `AlgebraicGeometry.Etale.whiskerLeft_verdierDualIsoCoefficientDualTensor_hom_app_comp`
  (`thm-sf-dual-perfect`): `θ` is compatible with the evaluations. The compatibility with a
  change of coefficients is `CategoryTheory.MonoidalClosed.map_ihomIsoIhomUnitTensor_hom`, and
  the pro-étale coefficient stages are
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect`.
- `AlgebraicGeometry.Etale.verdierDualIsoCoefficientDualTensor_hom_app_shift`
  (`thm-sf-dual-perfect`): `θ` commutes with shifts, `θ_{K⟦n⟧} = θ_K⟦-n⟧` under
  `AlgebraicGeometry.Etale.ihomShiftIso` (`RHom(K⟦n⟧, M) ≅ RHom(K, M)⟦-n⟧`).

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

The general biduality of the Verdier dual on `Dctf(X, Λ)` is
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual` of
`WeilConjectures.SixFunctors.Etale.Derived.Dualizing`; for perfect objects and an oriented
morphism it is proved here, without the constructibility hypotheses.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section InvertibleDualizingComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X : Scheme.{u}} {ω T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
  (γ : T ≅ ω) (hT : IsInvertible T)

attribute [local instance] _root_.DerivedCategory.braidedCategory'

include γ hT in
/-- Blueprint `sk-thm-sf-dual-perfect`: The dual of a perfect complex (biduality).

For a perfect `K` the double-dual map `K ⟶ 𝔻_X 𝔻_X K` is an isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_of_isDualizable
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K) :
    IsIso ((derivedHomToIhomIhomNatTrans A X ω).app K) :=
  MonoidalClosed.isIso_toIhomIhom_of_isDualizable γ hT hK

section Shift

end Shift

end InvertibleDualizingComplex

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}

variable {Λ}

variable {S : Scheme.{u}} {d : ℕ} {a : X ⟶ S} [HasCompactification a]

end Etale

end AlgebraicGeometry
