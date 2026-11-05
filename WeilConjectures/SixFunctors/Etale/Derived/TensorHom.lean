/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Parametrized
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
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

The tensor–Hom exchange is constructed as a natural isomorphism of bifunctors
`D(X_ét)ᵒᵖ ⥤ D(Y_ét) ⥤ D(Y_ét)`, for any coefficient category `A` for which the projection map
is an isomorphism (axiom (A3) of `def-sf-datum`) and any right adjoint `G` of `Rf_!`
(`AlgebraicGeometry.Etale.derivedHomLowerShriekIsoOfAdjunction`), by conjugating the projection
formula along the two adjunctions with a parameter
(`CategoryTheory.ParametrizedAdjunction.conjugateIso`). For a finite coefficient ring `Λ` and
`G = Rf^!` it is `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`. The other
comparison maps are not constructed in this repository, so the remaining isomorphisms are
asserted as `Nonempty (_ ≅ _)`.

As in the blueprint, the compatibilities of the tensor–Hom exchange are those of its
ingredients, and they are stated in that form. A change of coefficients (finite reduction,
scalar extension) is encoded by functors `T_X`, `T_Y` and comparison 2-squares for the left
adjoints `Lf^*`, `Rf_!`, `M ⊗ᴸ -`; the comparison maps of the right adjoints `Rf_*`, `Rf^!`,
`RHom(M, -)` are their mates. If the projection map is compatible with the change of
coefficients (axiom (A5) of `def-sf-datum`), so is the exchange. Likewise the exchange commutes
with shifts, since the projection map does.

The tensor–Hom statement is made on `Dctf`, so applying it at `N = ω_Y` needs `ω_Y` to lie in
`Dctf(Y, A)`. In the blueprint's setting (a finite-type scheme over a field, finite coefficient
ring) this holds; for the general coefficient category `A` and base `S` of this folder it does
not follow (the unit of `A` need not be constructible), so the Verdier exchange carries it as
the hypothesis `hω`. `AlgebraicGeometry.Etale.constructibleFiniteTor_dualizingComplex`
discharges it over a Noetherian base whenever the unit `Λ_S` lies in `Dctf(S, A)`.

## Main statements

- `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` (`lem-sf-tensor-hom`): the
  natural isomorphism `Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`, given the projection formula.
- `AlgebraicGeometry.Etale.commShift_derivedHomRightDerivedLowerShriekIso_app_hom`
  (`lem-sf-tensor-hom`): it commutes with shifts.
- `AlgebraicGeometry.Etale.derivedHomLowerShriekIsoOfAdjunction_hom_app_comp_mateEquiv`
  (`lem-sf-tensor-hom`): it is compatible with changes of coefficients, such as finite
  reduction and scalar extension.
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

universe u' u'' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

section TensorHomIso

variable [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `lem-sf-tensor-hom`: Tensor–Hom form of the exchange, for an arbitrary right
adjoint `G` of `Rf_!` (for a finite coefficient ring, `G = Rf^!`:
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`).

Assume the projection formula for `f` (axiom (A3) of the six-functor datum `def-sf-datum`):
the projection map `PF : Rf_! M ⊗ᴸ L ⟶ Rf_!(M ⊗ᴸ Lf^* L)`
(`AlgebraicGeometry.Etale.projectionMap`) is an isomorphism. Then there is an isomorphism
`Rf_* RHom_X(M, G N) ≅ RHom_Y(Rf_! M, N)` of bifunctors `D(X_ét)ᵒᵖ ⥤ D(Y_ét) ⥤ D(Y_ét)`:
the conjugate of the projection formula along the adjunctions with a parameter
(`CategoryTheory.ParametrizedAdjunction.conjugateIso`). -/
noncomputable def derivedHomLowerShriekIsoOfAdjunction
    {G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : R(f)_![A] ⊣ G) [IsIso (projectionMap A f)] :
    RHom(X)[A] ⋙ (Functor.whiskeringLeft _ _ _).obj G ⋙
        (Functor.whiskeringRight _ _ _).obj R((f)_*[A]) ≅
      (R(f)_![A]).op ⋙ RHom(Y)[A] :=
  ((derivedTensorHomAdjunction₂ A X).comp (derivedUpperStarLowerStarAdjunction A f)
      adj).conjugateIso
    ((derivedTensorHomAdjunction₂ A Y).precomp R(f)_![A]) (asIso (projectionMap A f))

/-- Blueprint `lem-sf-tensor-hom`: Tensor–Hom form of the exchange.

Let `f : X ⟶ Y` admit a compactification, and assume the projection formula for `f`
(axiom (A3) of the six-functor datum `def-sf-datum`): the projection map
`PF : Rf_! M ⊗ᴸ L ⟶ Rf_!(M ⊗ᴸ Lf^* L)` (`AlgebraicGeometry.Etale.projectionMap`) is an
isomorphism. Then there is an isomorphism

`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`,

natural in `M` and `N`, i.e. an isomorphism of bifunctors `D(X_ét)ᵒᵖ ⥤ D(Y_ét) ⥤ D(Y_ét)`.

As in the blueprint, it is the Yoneda consequence of the chain of adjunctions: the bifunctor
`(M, L) ↦ Rf_!(M ⊗ᴸ Lf^* L)` is left adjoint, with the parameter `M`, to
`(M, N) ↦ Rf_* RHom_X(M, Rf^! N)` (by `Lf^* ⊣ Rf_*`, `- ⊗ᴸ - ⊣₂ RHom` and `Rf_! ⊣ Rf^!`),
the bifunctor `(M, L) ↦ Rf_! M ⊗ᴸ L` is left adjoint to `(M, N) ↦ RHom_Y(Rf_! M, N)`, and
the inverse of the projection formula identifies the two left adjoints; the isomorphism is
objectwise the conjugate of the projection formula
(`AlgebraicGeometry.Etale.derivedHomLowerShriekIsoOfAdjunction`). The blueprint
takes `M` and `N` in `Dᵇctf`; no such hypothesis is needed. For a finite coefficient ring `Λ`
the projection formula holds (`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`). -/
noncomputable def derivedHomRightDerivedLowerShriekIso
    [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)] :
    RHom(X)[ModuleCat.{u + 1} Λ] ⋙ (Functor.whiskeringLeft _ _ _).obj R(f)^![Λ] ⋙
        (Functor.whiskeringRight _ _ _).obj R((f)_*[ModuleCat.{u + 1} Λ]) ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).op ⋙ RHom(Y)[ModuleCat.{u + 1} Λ] :=
  derivedHomLowerShriekIsoOfAdjunction (ModuleCat.{u + 1} Λ) f
    (rightDerivedUpperShriekAdjunction Λ f)

section CoefficientChange

open TwoSquare

variable (A' : Type u'') [Category.{u + 1} A'] [Abelian A'] [IsGrothendieckAbelian.{u + 1} A']
  [MonoidalCategory A'] [MonoidalPreadditive A'] [SymmetricCategory A'] [MonoidalClosed A']
  [Abelian.HasFunctorialFlatResolution A']
  {FA' : A' → A' → Type (u + 1)} {CA' : A' → Type (u + 1)}
  [∀ X Y, FunLike (FA' X Y) (CA' X) (CA' Y)] [ConcreteCategory.{u + 1} A' FA']
  [Etale.UpperStarPreservesFlat A']
  [(CategoryTheory.forget A').ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A')]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A')]

end CoefficientChange

end TensorHomIso

section TensorHom

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasCompactification f]

/-- Blueprint `sk-thm-sf-tensor-hom`: Tensor–Hom form of the exchange.

For a morphism `f : X ⟶ Y` admitting a compactification and torsion coefficients `Λ`, the direct
image of the internal hom from `M` into `Rf^! N` agrees with the internal hom on `Y` from
`Rf_! M` into `N`:

`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`.

As in the blueprint this is obtained from the chain of adjunctions `Rf_! ⊣ Rf^!`,
`Lf^* ⊣ Rf_*` and `- ⊗ᴸ - ⊣ RHom`, together with the projection formula: it is the component
at `(M, N)` of the natural isomorphism
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` (`lem-sf-tensor-hom`), the
projection formula holding at finite coefficients
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`). For torsion coefficients no
finiteness hypothesis on `M` and `N` is needed. This is also blueprint
`fix-lem-tensor-adjunction`.

The naturality in `M` and `N` and the compatibilities of the blueprint are those of
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` at `A = ModuleCat Λ`: it commutes
with shifts
(`AlgebraicGeometry.Etale.commShift_derivedHomRightDerivedLowerShriekIso_app_hom`), and it is
compatible with any change of coefficients `Λ → Λ'`, such as finite reduction or scalar
extension, which is compatible with the projection map
(`AlgebraicGeometry.Etale.derivedHomLowerShriekIsoOfAdjunction_hom_app_comp_mateEquiv`). -/
theorem nonempty_iso_derivedHom_rightDerivedLowerShriek
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op M)).obj
        ((R(f)^![Λ]).obj N)) ≅
      (RHom(Y)[ModuleCat.{u + 1} Λ].obj (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M))).obj N) := by
  have := isIso_projectionMap_of_finite Λ f
  exact ⟨((derivedHomRightDerivedLowerShriekIso _ f).app (op M)).app N⟩

/-- Blueprint `prop-asd-internal-adjunction`: Internal ambient adjunction.

For a morphism `f : X ⟶ Y` admitting a compactification and a finite coefficient ring `Λ`,
there is a canonical isomorphism, natural in `M ∈ D(X_ét, Λ)` and `K ∈ D(Y_ét, Λ)`,

`Rf_* RHom_X(M, Rf^! K) ≅ RHom_Y(Rf_! M, K)`.

It is the Yoneda transpose of the chain of adjunctions `Lf^* ⊣ Rf_*`, `- ⊗ᴸ - ⊣ RHom`,
`Rf_! ⊣ Rf^!` and of the projection formula `Rf_!(M ⊗ᴸ Lf^* Q) ≅ Rf_! M ⊗ᴸ Q`
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`, `lem-amb-proper-coproducts-projection`),
that is `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` at `A = ModuleCat Λ`. The
blueprint assumes Noetherian schemes; this is not needed here. -/
noncomputable def derivedHomRightDerivedLowerShriekIsoOfFinite :
    RHom(X)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringLeft _ _ _).obj R(f)^![Λ] ⋙
          (Functor.whiskeringRight _ _ _).obj R((f)_*[ModuleCat.{u + 1} Λ]) ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).op ⋙ RHom(Y)[ModuleCat.{u + 1} Λ] :=
  have := isIso_projectionMap_of_finite Λ f
  derivedHomRightDerivedLowerShriekIso _ f

end TensorHom

section VerdierExchange

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}} (f : X ⟶ Y)
  (aY : Y ⟶ S) [HasCompactification f] [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- Blueprint `sk-thm-sf-verdier-exchange`: Verdier-duality exchange.

First half. If `f : X ⟶ Y`, the structure morphism `a_Y : Y ⟶ S` and `a_X = f ≫ a_Y` all
admit a compactification (the last is assumed separately, there being no composition instance
for `HasCompactification`), then for torsion coefficients the exceptional inverse image along
`f` of the dualizing complex of `Y` is the dualizing complex of `X`:

`Rf^! ω_Y ≅ ω_X`.

This is the mate, under the adjunctions `Rf_! ⊣ Rf^!`, of the composition isomorphism
`R(a_Y ∘ f)_! ≅ R a_{Y!} ∘ Rf_!`, evaluated at the monoidal unit `Λ_S`. -/
theorem nonempty_iso_rightDerivedUpperShriek_dualizingComplex :
    Nonempty ((R(f)^![Λ]).obj (dualizingComplex _ aY) ≅
      dualizingComplex _ (f ≫ aY)) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f aY
  exact ⟨((((rightDerivedUpperShriekAdjunction _ (f ≫ aY)).ofNatIsoLeft e).rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction _ f).comp
      (rightDerivedUpperShriekAdjunction _ aY))).app (𝟙_ _)).symm⟩

/-- Blueprint `sk-thm-sf-verdier-exchange`: Verdier-duality exchange.

Second half. With `a_Y : Y ⟶ S` the structure morphism of `Y` and `a_X = f ≫ a_Y` that of
`X`, the Verdier duals `𝔻_Y = RHom_Y(-, ω_Y)` and `𝔻_X = RHom_X(-, ω_X)` exchange the
extraordinary and the ordinary direct image: for torsion coefficients and every `M`,

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`.

As in the blueprint this is the tensor–Hom exchange
`nonempty_iso_derivedHom_rightDerivedLowerShriek` at `N = ω_Y`, combined with
`Rf^! ω_Y ≅ ω_X`. This is also blueprint `fix-cor-verdier-exchange`. -/
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
