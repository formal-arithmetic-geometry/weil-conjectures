/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The projection formula and finite reduction of the coefficients

Let `Λ` be a coefficient ring and `J` an ideal of `Λ`. In this repository the reduction of
coefficients `K ↦ K_m` along `Λ ⟶ Λ/J` is the endofunctor
`ρ = AlgebraicGeometry.Etale.reductionModIdeal`, `K ↦ K ⊗ᴸ (Λ/J)_X`, of `D(X_ét, Λ)`: the
reduction `K_m` is kept as a complex of `Λ`-modules. Read in `D(Λ)`, a tensor product over
`Λ/J` of two reduced complexes is `K_m ⊗ᴸ_{Λ/J} L_m = K ⊗ᴸ_Λ L_m`, and `Rf_!` commutes with
reduction, so the projection map `PF_{f, K_m, L_m}` of the blueprint becomes the projection map
`PF_{f, K, ρL}` over `Λ`.

The three compatibilities of `ρ` used in blueprint `sk-prop-sf-pf-reduction` are:

* with `⊗ᴸ`: the associator `ρ(M ⊗ᴸ L) = (M ⊗ᴸ L) ⊗ᴸ (Λ/J)_Y ≅ M ⊗ᴸ ρL`;
* with `Lf^*`: `Lf^*(ρL) ≅ ρ(Lf^*L)`, the tensor comparison of `Lf^*` followed by
  `Lf^*(Λ/J)_Y ≅ (Λ/J)_X` (`AlgebraicGeometry.Etale.leftDerivedUpperStarReductionModIdealIso`);
* with `Rf_!`: `ρ(Rf_!K) ⟶ Rf_!(ρK)`, the projection map at `(K, (Λ/J)_Y)` followed by
  `Lf^*(Λ/J)_Y ≅ (Λ/J)_X` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekReductionModIdealMap`).
  It is an isomorphism for `Λ` finite, by the finite projection formula.

Everything except the identification of the constant complexes is formal, and is done for an
arbitrary coefficient category `A` and an arbitrary object `N` in place of `(Λ/J)_Y`. The square
is stated for a general coefficient category: at `A = ModuleCat Λ`, writing the monoidal
structure of `D(X_ét, Λ)` through instance search produces a term the kernel cannot compare
with the one inside `AlgebraicGeometry.Etale.derivedTensor` in reasonable time (see the
implementation notes of `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).

When `Λ/ϖⁿ` is perfect, that is for `J = (ϖⁿ)` with `ϖ` a nonzerodivisor (for `Λ = 𝒪_E`, the
reduction `𝒪_E ⟶ A_{E,n}`), the constant complex `(Λ/ϖⁿ)_X` is dualizable, and the comparisons
of `ρ` with `Rf_!` and `Rf_*` are isomorphisms for every `Λ` (blueprint
`lem-fix-operation-reduction`).

## Main statements

- `AlgebraicGeometry.Etale.projectionMapOfCompactification_constantSingle`
  (`sk-prop-sf-pf-reduction`, `prop-sf-pf-reduction`): the square comparing `ρ(PF_{f, K, L})`
  and `PF_{f, K, ρL}` through the three compatibilities commutes.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMapOfCompactification_iff`,
  `AlgebraicGeometry.Etale.hasProjectionFormula_iff_reductionModIdeal`: hence, for `Λ` finite,
  `ρ(PF_{f, K, L})` is an isomorphism if and only if `PF_{f, K, ρL}` is, and the projection
  formula holds at `(K, L)` if and only if it holds at `(K, ρL)`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekReductionModIdealMap_span_pow`,
  `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarReductionModIdealMap_span_pow`
  (`lem-fix-operation-reduction`): reduction modulo `ϖⁿ` commutes with `Rf_!` and `Rf_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {X Y : Scheme.{u}}

/-- For `a : Lf^*N_Y ≅ N_X`, the isomorphism `Lf^*(L ⊗ᴸ N_Y) ≅ Lf^*L ⊗ᴸ N_X`, natural in `L`:
the tensor comparison of `Lf^*` followed by `a`. -/
noncomputable def leftDerivedUpperStarDerivedTensorRightIso (f : X ⟶ Y)
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX) :
    derivedTensorRight A Y NY ⋙ L((f)^*[A]) ≅ L((f)^*[A]) ⋙ derivedTensorRight A X NX :=
  derivedTensorRightCompLeftDerivedUpperStarIso A f NY ≪≫
    Functor.isoWhiskerLeft L((f)^*[A]) ((derivedTensorRightFunctor A X).mapIso a)

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {f : X ⟶ Y} (c : Compactification f)

end General

section Constant

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable {X Y : Scheme.{u}}

/-- The constant complex `M_X ∈ D(X_ét)` on an object `M` of the coefficient category: the
constant sheaf with value `M`, placed in degree zero. -/
noncomputable abbrev constantSingle (X : Scheme.{u}) (M : A) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf X.smallEtaleTopology A).obj M)

/-- **The derived pullback of a constant complex is constant**: `Lf^*(M_Y) ≅ M_X`. The pullback
`f^*` is exact, so `Lf^*` is computed termwise
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`), and `f^*` carries
constant sheaves to constant sheaves (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`). -/
noncomputable def leftDerivedUpperStarSingleConstantSheafIso (f : X ⟶ Y) (M : A) :
    L((f)^*[A]).obj (constantSingle A Y M) ≅ constantSingle A X M :=
  (leftDerivedUpperStarIsoMapDerivedCategory A f).app _ ≪≫
    ((f)^*[A].mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ((Scheme.upperStarConstantSheafIso A f).app M)

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {f : X ⟶ Y} (c : Compactification f)

end Constant

section Module

variable (Λ : Type (u + 1)) [CommRing Λ] (J : Ideal Λ) {X Y : Scheme.{u}}

attribute [local instance] Scheme.Etale.essentiallySmall

variable {f : X ⟶ Y} (c : Compactification f)

end Module

end Etale

end AlgebraicGeometry
