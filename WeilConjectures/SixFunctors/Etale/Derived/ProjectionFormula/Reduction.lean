/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
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
arbitrary coefficient category `A` and an arbitrary object `N` in place of `(Λ/J)_Y`.

## Main statements

- `AlgebraicGeometry.Etale.projectionMap_reductionModIdeal`: the square comparing
  `ρ(PF_{f, K, L})` and `PF_{f, K, ρL}` through the three compatibilities commutes (blueprint
  `sk-prop-sf-pf-reduction`).
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMap_iff`: hence, for `Λ`
  finite, `ρ(PF_{f, K, L})` is an isomorphism if and only if `PF_{f, K, ρL}` is.
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

lemma leftDerivedUpperStarDerivedTensorRightIso_hom_app (f : X ⟶ Y)
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarDerivedTensorRightIso A f a).hom.app L =
      ((leftDerivedUpperStarTensorComparison A f).app L).app NY ≫
        L((f)^*[A]).obj L ◁ a.hom :=
  rfl

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {f : X ⟶ Y} (c : Compactification f)

/-- For `a : Lf^*N_Y ⟶ N_X`, the comparison `Rf_!K ⊗ᴸ N_Y ⟶ Rf_!(K ⊗ᴸ N_X)`, natural in `K`: the
projection map `PF_{K, N_Y}` followed by `Rf_!(K ◁ a)`. -/
noncomputable def rightDerivedLowerShriekDerivedTensorRightMap
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ⟶ NX) :
    Rf_!(c)[A] ⋙ derivedTensorRight A Y NY ⟶ derivedTensorRight A X NX ⋙ Rf_!(c)[A] where
  app K := ((projectionMapOfCompactification A c).app K).app NY ≫
    Rf_!(c)[A].map (K ◁ a)
  naturality _ _ φ := Adjunction.projectionMap_comp_map_whiskerLeft_naturality
    (fun K L ↦ ((projectionMapOfCompactification A c).app K).app L) a
    (fun φ L ↦ NatTrans.congr_app ((projectionMapOfCompactification A c).naturality φ) L) φ

lemma rightDerivedLowerShriekDerivedTensorRightMap_app
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ⟶ NX)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerShriekDerivedTensorRightMap A c a).app K =
      ((projectionMapOfCompactification A c).app K).app NY ≫ Rf_!(c)[A].map (K ◁ a) :=
  rfl

/-- **The reduction square of the projection map, for a general coefficient object.** For
`a : Lf^*N_Y ≅ N_X`, `K` on `X` and `L` on `Y`, the square
```
(Rf_!K ⊗ᴸ L) ⊗ᴸ N_Y ---PF_{K, L} ▷ N_Y---> Rf_!(K ⊗ᴸ Lf^*L) ⊗ᴸ N_Y
        | α                                            | comparison of Rf_! and - ⊗ᴸ N
        v                                              v
Rf_!K ⊗ᴸ (L ⊗ᴸ N_Y)                           Rf_!((K ⊗ᴸ Lf^*L) ⊗ᴸ N_X)
        | PF_{K, L ⊗ᴸ N_Y}                             ^ Rf_! α⁻¹
        v                                              |
Rf_!(K ⊗ᴸ Lf^*(L ⊗ᴸ N_Y)) --Rf_!(K ◁ (δ ≫ 1 ◁ a))--> Rf_!(K ⊗ᴸ (Lf^*L ⊗ᴸ N_X))
```
commutes. It follows from the associativity of the projection map
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`). -/
theorem projectionMapOfCompactification_derivedTensorRight
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (derivedTensorRight A Y NY).map (((projectionMapOfCompactification A c).app K).app L) ≫
        (rightDerivedLowerShriekDerivedTensorRightMap A c a.hom).app
          (K ⊗ L((f)^*[A]).obj L) =
      (α_ ((Rf_!(c)[A]).obj K) L NY).hom ≫
        ((projectionMapOfCompactification A c).app K).app (L ⊗ NY) ≫
        Rf_!(c)[A].map (K ◁ (leftDerivedUpperStarDerivedTensorRightIso A f a).hom.app L) ≫
        Rf_!(c)[A].map (α_ K (L((f)^*[A]).obj L) NX).inv :=
  Adjunction.projectionMap_whiskerRight_comp
    (fun K L ↦ ((projectionMapOfCompactification A c).app K).app L)
    (projectionMapOfCompactification_assoc A c) a.hom K L

/-- **Invertibility through the reduction square, for a general coefficient object.** If the
comparison `Rf_!M ⊗ᴸ N_Y ⟶ Rf_!(M ⊗ᴸ N_X)` is an isomorphism at `M = K ⊗ᴸ Lf^*L`, then
`PF_{K, L} ⊗ᴸ N_Y` is an isomorphism if and only if `PF_{K, L ⊗ᴸ N_Y}` is. -/
theorem isIso_derivedTensorRight_map_projectionMapOfCompactification_iff
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hc : IsIso ((rightDerivedLowerShriekDerivedTensorRightMap A c a.hom).app
      (K ⊗ L((f)^*[A]).obj L))) :
    IsIso ((derivedTensorRight A Y NY).map (((projectionMapOfCompactification A c).app K).app L))
      ↔ IsIso (((projectionMapOfCompactification A c).app K).app (L ⊗ NY)) :=
  Adjunction.isIso_projectionMap_whiskerRight_iff
    (fun K L ↦ ((projectionMapOfCompactification A c).app K).app L)
    (projectionMapOfCompactification_assoc A c) a.hom K L hc

end General

end Etale

end AlgebraicGeometry
