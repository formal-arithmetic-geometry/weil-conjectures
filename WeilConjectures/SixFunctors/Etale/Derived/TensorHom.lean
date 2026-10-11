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
`D(X_ét)ᵒᵖ ⥤ D(Y_ét) ⥤ D(Y_ét)` (`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`),
for any coefficient category `A` for which the projection map is an isomorphism (axiom (A3) of
`def-sf-datum`), by conjugating the projection formula along the two adjunctions with a
parameter (`CategoryTheory.ParametrizedAdjunction.conjugateIso`). The other comparison maps are
not constructed in this repository, so the remaining isomorphisms are asserted as
`Nonempty (_ ≅ _)`.

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
- `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv`
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

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

section TensorHomIso

variable [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]

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
(`CategoryTheory.ParametrizedAdjunction.conjugateIso`). The blueprint takes `M` and `N` in
`Dᵇctf`; no such hypothesis is needed. For a finite coefficient ring `Λ` the projection
formula holds (`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`). -/
noncomputable def derivedHomRightDerivedLowerShriekIso [IsIso (projectionMap A f)] :
    RHom(X)[A] ⋙ (Functor.whiskeringLeft _ _ _).obj R(f)^![A] ⋙
        (Functor.whiskeringRight _ _ _).obj R((f)_*[A]) ≅
      (R(f)_![A]).op ⋙ RHom(Y)[A] :=
  ((derivedTensorHomAdjunction₂ A X).comp (derivedUpperStarLowerStarAdjunction A f)
      (rightDerivedUpperShriekAdjunction A f)).conjugateIso
    ((derivedTensorHomAdjunction₂ A Y).precomp R(f)_![A]) (asIso (projectionMap A f))

omit [HasSmallSiteSheafify A] in
/-- Blueprint `lem-sf-tensor-hom`: Tensor–Hom form of the exchange, compatibility with shifts.

The isomorphism `Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)` of
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` commutes with the shifts in
`N`. Both sides carry the shift structures of the functors they are built from
(`AlgebraicGeometry.Etale.commShiftDerivedHomObj` for `RHom(M, -)`).

As in the blueprint, the compatibility is that of the ingredients: the isomorphism is the
conjugate of the projection map `Rf_! M ⊗ᴸ L ⟶ Rf_!(M ⊗ᴸ Lf^* L)`, which commutes with the
shifts in `L` (`AlgebraicGeometry.Etale.commShift_projectionMap_app`), along the adjunctions
`Lf^* ⊣ Rf_*`, `Rf_! ⊣ Rf^!` and `K ⊗ᴸ - ⊣ RHom(K, -)`, which commute with shifts
(`AlgebraicGeometry.Etale.commShift_derivedUpperStarLowerStarAdjunction`,
`AlgebraicGeometry.Etale.commShift_rightDerivedUpperShriekAdjunction`,
`AlgebraicGeometry.Etale.commShift_derivedTensorHomAdjunction`), and conjugation preserves
the compatibility with shifts (`CategoryTheory.NatTrans.CommShift.conjugateEquiv`). -/
theorem commShift_derivedHomRightDerivedLowerShriekIso_app_hom [IsIso (projectionMap A f)]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift (F₁ := (R(f)^![A] ⋙ (RHom(X)[A]).obj (op M)) ⋙ R((f)_*[A]))
      (F₂ := (RHom(Y)[A]).obj (op ((R(f)_![A]).obj M)))
      ((derivedHomRightDerivedLowerShriekIso A f).app (op M)).hom ℤ :=
  NatTrans.CommShift.conjugateEquiv
    ((derivedUpperStarLowerStarAdjunction A f).comp
      ((derivedTensorHomAdjunction A M).comp (rightDerivedUpperShriekAdjunction A f)))
    (derivedTensorHomAdjunction A ((R(f)_![A]).obj M)) ((projectionMap A f).app M)

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
  [(R(f)_![A']).IsLeftAdjoint]

omit [HasSmallSiteSheafify A] in
/-- Blueprint `lem-sf-tensor-hom`: Tensor–Hom form of the exchange, compatibility with
finite reduction and scalar extension, as an identity of 2-squares.

This is `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv`
before evaluation at an object `N`: the isomorphism over `A` followed by the comparison map
`T_Y RHom(Rf_! M, -) ⟶ RHom(Rf_! M', T_Y -)` is the composite comparison map
`T_Y Rf_* RHom(M, Rf^! -) ⟶ Rf_* RHom(M', Rf^! T_Y -)` followed by the isomorphism over `A'`.
-/
theorem whiskerTop_derivedHomRightDerivedLowerShriekIso_hom [IsIso (projectionMap A f)]
    [IsIso (projectionMap A' f)]
    (TX : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (TY : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A'))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M' : DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (σ : TwoSquare TY L((f)^*[A]) L((f)^*[A']) TX)
    (μ : TwoSquare TX ((-⊗ᴸ-(X)[A]).obj M) ((-⊗ᴸ-(X)[A']).obj M') TX)
    (ρ : TwoSquare TX R(f)_![A] R(f)_![A'] TY)
    (ν : TwoSquare TY ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj M))
      ((-⊗ᴸ-(Y)[A']).obj ((R(f)_![A']).obj M')) TY)
    (h : ν.whiskerLeft ((projectionMap A f).app M) =
      (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight ((projectionMap A' f).app M')) :
    (mateEquiv (derivedTensorHomAdjunction A ((R(f)_![A]).obj M))
        (derivedTensorHomAdjunction A' ((R(f)_![A']).obj M')) ν).whiskerTop
        ((derivedHomRightDerivedLowerShriekIso A f).app (op M)).hom =
      ((mateEquiv (rightDerivedUpperShriekAdjunction A f)
            (rightDerivedUpperShriekAdjunction A' f) ρ ≫ₕ
          mateEquiv (derivedTensorHomAdjunction A M) (derivedTensorHomAdjunction A' M') μ) ≫ₕ
          mateEquiv (derivedUpperStarLowerStarAdjunction A f)
            (derivedUpperStarLowerStarAdjunction A' f) σ).whiskerBottom
        ((derivedHomRightDerivedLowerShriekIso A' f).app (op M')).hom := by
  rw [← mateEquiv_hcomp, ← mateEquiv_hcomp]
  exact mateEquiv_whiskerTop_conjugateEquiv
    ((derivedUpperStarLowerStarAdjunction A f).comp
      ((derivedTensorHomAdjunction A M).comp (rightDerivedUpperShriekAdjunction A f)))
    (derivedTensorHomAdjunction A ((R(f)_![A]).obj M))
    ((derivedUpperStarLowerStarAdjunction A' f).comp
      ((derivedTensorHomAdjunction A' M').comp (rightDerivedUpperShriekAdjunction A' f)))
    (derivedTensorHomAdjunction A' ((R(f)_![A']).obj M'))
    ((projectionMap A f).app M) ((projectionMap A' f).app M') _ ν h

omit [HasSmallSiteSheafify A] in
/-- Blueprint `lem-sf-tensor-hom`: Tensor–Hom form of the exchange, compatibility with
finite reduction and scalar extension.

A change of coefficients, such as the finite reduction `A_{E,n} → A_{E,m}` or the scalar
extension `A_{E,n} → A_{E',n}`, is given by functors `T_X : D(X_ét, A) ⥤ D(X_ét, A')` and
`T_Y : D(Y_ét, A) ⥤ D(Y_ét, A')`, an object `M'` corresponding to `M` (typically `T_X M`), and
comparison maps for the left adjoints, written as 2-squares:

* `σ : Lf^*(T_Y L) ⟶ T_X(Lf^* L)` for the derived pullback,
* `μ : M' ⊗ᴸ T_X K ⟶ T_X(M ⊗ᴸ K)` and `ν : Rf_! M' ⊗ᴸ T_Y L ⟶ T_Y(Rf_! M ⊗ᴸ L)` for the
  tensor products,
* `ρ : Rf_!(T_X K) ⟶ T_Y(Rf_! K)` for the direct image with compact support.

Their mates (`CategoryTheory.mateEquiv`) are the comparison maps of the right adjoints
`T_Y(Rf_* K) ⟶ Rf_*(T_X K)`, `T_X RHom(M, K) ⟶ RHom(M', T_X K)`,
`T_Y RHom(Rf_! M, L) ⟶ RHom(Rf_! M', T_Y L)` and `T_X(Rf^! L) ⟶ Rf^!(T_Y L)`.

Assume that the change of coefficients is compatible with the projection formula (axiom (A5)
of `def-sf-datum` for the projection transformation): `ν` followed by the projection map over
`A` is the projection map over `A'` followed by the composite of `σ`, `μ` and `ρ`. Then the
isomorphism `Rf_* RHom(M, Rf^! N) ≅ RHom(Rf_! M, N)` of
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` is compatible with the change of
coefficients: the square

```
T_Y Rf_* RHom(M, Rf^! N) -------- T_Y(iso) --------> T_Y RHom(Rf_! M, N)
          |                                                  |
          | comparison                                       | comparison
          v                                                  v
Rf_* RHom(M', Rf^! T_Y N) ---------- iso ----------> RHom(Rf_! M', T_Y N)
```

commutes, where the left vertical map is the composite
`T_Y Rf_* ⟶ Rf_* T_X ⟶ Rf_* RHom(M', T_X -) ⟶ Rf_* RHom(M', Rf^! T_Y -)`. As in the
blueprint, this is the compatibility of the ingredients
(`AlgebraicGeometry.Etale.whiskerTop_derivedHomRightDerivedLowerShriekIso_hom`). -/
theorem derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv [IsIso (projectionMap A f)]
    [IsIso (projectionMap A' f)]
    (TX : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (TY : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A'))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M' : DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (σ : TwoSquare TY L((f)^*[A]) L((f)^*[A']) TX)
    (μ : TwoSquare TX ((-⊗ᴸ-(X)[A]).obj M) ((-⊗ᴸ-(X)[A']).obj M') TX)
    (ρ : TwoSquare TX R(f)_![A] R(f)_![A'] TY)
    (ν : TwoSquare TY ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj M))
      ((-⊗ᴸ-(Y)[A']).obj ((R(f)_![A']).obj M')) TY)
    (h : ν.whiskerLeft ((projectionMap A f).app M) =
      (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight ((projectionMap A' f).app M'))
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    TY.map (((derivedHomRightDerivedLowerShriekIso A f).app (op M)).hom.app N) ≫
        (mateEquiv (derivedTensorHomAdjunction A ((R(f)_![A]).obj M))
          (derivedTensorHomAdjunction A' ((R(f)_![A']).obj M')) ν).app N =
      (mateEquiv (derivedUpperStarLowerStarAdjunction A f)
          (derivedUpperStarLowerStarAdjunction A' f) σ).app _ ≫
        R((f)_*[A']).map ((mateEquiv (derivedTensorHomAdjunction A M)
          (derivedTensorHomAdjunction A' M') μ).app _) ≫
        R((f)_*[A']).map (((RHom(X)[A']).obj (op M')).map
          ((mateEquiv (rightDerivedUpperShriekAdjunction A f)
            (rightDerivedUpperShriekAdjunction A' f) ρ).app N)) ≫
        ((derivedHomRightDerivedLowerShriekIso A' f).app (op M')).hom.app (TY.obj N) := by
  have key := congr_app
    (whiskerTop_derivedHomRightDerivedLowerShriekIso_hom A f A' TX TY M M' σ μ ρ ν h) N
  simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app, TwoSquare.hComp_app,
    Functor.comp_obj, Category.assoc, Functor.map_comp] at key
  exact key

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
finiteness hypothesis on `M` and `N` is needed.

The naturality in `M` and `N` and the compatibilities of the blueprint are those of
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` at `A = ModuleCat Λ`: it commutes
with shifts
(`AlgebraicGeometry.Etale.commShift_derivedHomRightDerivedLowerShriekIso_app_hom`), and it is
compatible with any change of coefficients `Λ → Λ'`, such as finite reduction or scalar
extension, which is compatible with the projection map
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv`). -/
theorem nonempty_iso_derivedHom_rightDerivedLowerShriek
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op M)).obj
        ((R(f)^![ModuleCat.{u + 1} Λ]).obj N)) ≅
      (RHom(Y)[ModuleCat.{u + 1} Λ].obj (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M))).obj N) := by
  have := isIso_projectionMap_of_finite Λ f
  exact ⟨((derivedHomRightDerivedLowerShriekIso _ f).app (op M)).app N⟩

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
