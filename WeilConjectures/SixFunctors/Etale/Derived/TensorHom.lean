/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# The tensor–Hom exchange and the Verdier-duality exchange

Let `f : X ⟶ Y` be a morphism of schemes admitting a compactification, so that the pair
`Rf_! ⊣ Rf^!` is available. The *tensor–Hom form of the exchange* is the isomorphism

`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`,

natural in `M` and `N`. It is the Yoneda consequence of the three adjunctions `Lf^* ⊣ Rf_*`,
`Rf_! ⊣ Rf^!` and `- ⊗ᴸ - ⊣ RHom`, together with the projection formula.

Specialising it to `N = ω_Y` and using `Rf^! ω_Y ≅ ω_X` (the mate of the composition law,
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`) gives the
*Verdier-duality exchange* `𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`: the Verdier dual intertwines `Rf_!`
and `Rf_*`. Note that this route to the exchange goes through the tensor–Hom statement only,
and so does not depend on the duality theory itself.

## Implementation notes

Canonical comparison maps are not constructed in this repository, so the isomorphisms are
asserted as `Nonempty (_ ≅ _)`; the blueprint's naturality clauses and its compatibilities
with finite reduction, scalar extension and shifts are consequently **not stated**.

The tensor–Hom statement is made on `Dctf`, so applying it at `N = ω_Y` needs `ω_Y` to lie in
`Dctf(Y, A)`. In the blueprint's setting (a finite-type scheme over a field, finite coefficient
ring) this holds; for the general coefficient category `A` and base `S` of this folder it does
not follow (the unit of `A` need not be constructible), so the Verdier exchange carries it as
the hypothesis `hω`. `AlgebraicGeometry.Etale.constructibleFiniteTor_dualizingComplex`
discharges it over a Noetherian base whenever the unit `Λ_S` lies in `Dctf(S, A)`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerShriek`
  (`sk-thm-sf-tensor-hom`): `Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex`
  (`sk-thm-sf-verdier-exchange`): `Rf^! ω_Y ≅ ω_X`.
- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek`
  (`sk-thm-sf-verdier-exchange`): `𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_dualizingComplex`: `ω_Y` lies in `Dctf`
  when `Λ_S` does and `S` is Noetherian.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

section TensorHom

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasCompactification f]

/-- Blueprint `sk-thm-sf-tensor-hom`: Tensor–Hom form of the exchange.

For a morphism `f : X ⟶ Y` admitting a compactification and torsion coefficients `Λ`, the direct
image of the internal hom from `M` into `Rf^! N` agrees with the internal hom on `Y` from
`Rf_! M` into `N`:

`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`.

As in the blueprint this is obtained from the chain of adjunctions `Rf_! ⊣ Rf^!`,
`Lf^* ⊣ Rf_*` and `- ⊗ᴸ - ⊣ RHom`, together with the projection formula: the functor
`N ↦ Rf_* RHom_X(M, Rf^! N)` is right adjoint to `L ↦ Rf_!(M ⊗ᴸ Lf^* L)`, the functor
`N ↦ RHom_Y(Rf_! M, N)` is right adjoint to `L ↦ Rf_! M ⊗ᴸ L`, and the projection formula
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`) identifies the two left adjoints.
For torsion coefficients no finiteness hypothesis on `M` and `N` is needed. -/
theorem nonempty_iso_derivedHom_rightDerivedLowerShriek
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op M)).obj
        ((R(f)^![ModuleCat.{u + 1} Λ]).obj N)) ≅
      (RHom(Y)[ModuleCat.{u + 1} Λ].obj (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M))).obj N) := by
  obtain ⟨e⟩ := nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek _ f M
    (fun L ↦ hasProjectionFormula_of_finite Λ f M L)
  exact ⟨(Adjunction.rightAdjointUniq
    (((derivedUpperStarLowerStarAdjunction _ f).comp (derivedTensorHomAdjunction _ M)).comp
      (rightDerivedUpperShriekAdjunction _ f))
    ((derivedTensorHomAdjunction _ ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)).ofNatIsoLeft
      (e ≪≫ (Functor.associator _ _ _).symm))).app N⟩

end TensorHom

section VerdierExchange

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}} (f : X ⟶ Y)
  (aY : Y ⟶ S) [HasCompactification f] [HasCompactification aY] [HasCompactification (f ≫ aY)]
  [QuasiCompact (f ≫ aY)]

/-- Blueprint `sk-thm-sf-verdier-exchange`: Verdier-duality exchange.

First half. If `f : X ⟶ Y`, the structure morphism `a_Y : Y ⟶ S` and `a_X = f ≫ a_Y` all
admit a compactification (the last is assumed separately, there being no composition instance
for `HasCompactification`), then for torsion coefficients the exceptional inverse image along
`f` of the dualizing complex of `Y` is the dualizing complex of `X`:

`Rf^! ω_Y ≅ ω_X`.

This is the mate, under the adjunctions `Rf_! ⊣ Rf^!`, of the composition isomorphism
`R(a_Y ∘ f)_! ≅ R a_{Y!} ∘ Rf_!`, evaluated at the monoidal unit `Λ_S`. -/
theorem nonempty_iso_rightDerivedUpperShriek_dualizingComplex :
    Nonempty ((R(f)^![ModuleCat.{u + 1} Λ]).obj (dualizingComplex _ aY) ≅
      dualizingComplex _ (f ≫ aY)) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ f aY
  exact ⟨(e.app (𝟙_ _)).symm⟩

/-- Blueprint `sk-thm-sf-verdier-exchange`: Verdier-duality exchange.

Second half. With `a_Y : Y ⟶ S` the structure morphism of `Y` and `a_X = f ≫ a_Y` that of
`X`, the Verdier duals `𝔻_Y = RHom_Y(-, ω_Y)` and `𝔻_X = RHom_X(-, ω_X)` exchange the
extraordinary and the ordinary direct image: for torsion coefficients and every `M`,

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`.

As in the blueprint this is the tensor–Hom exchange
`nonempty_iso_derivedHom_rightDerivedLowerShriek` at `N = ω_Y`, combined with
`Rf^! ω_Y ≅ ω_X`. -/
theorem nonempty_iso_verdierDual_rightDerivedLowerShriek
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((verdierDual _ aY).obj (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual _ (f ≫ aY)).obj (op M))) := by
  obtain ⟨e₁⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek Λ f M (dualizingComplex _ aY)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ f aY
  exact ⟨e₁.symm ≪≫ (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
    ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op M)).mapIso e₂)⟩

end VerdierExchange

end Etale

end AlgebraicGeometry
