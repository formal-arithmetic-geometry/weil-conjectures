/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality

/-!
# The Verdier-duality exchange as a natural isomorphism

Let `f : X ⟶ Y` and `a_Y : Y ⟶ S` admit compactifications, with `a_X = f ≫ a_Y`, and let
`ω_X = Ra_X^! Λ_S`, `ω_Y = Ra_Y^! Λ_S` be the dualizing complexes. Given a composition
isomorphism `R(a_Y ∘ f)_! ≅ Ra_{Y!} ∘ Rf_!` (`sk-thm-sf-comp-composition`), its mate is an
isomorphism `Rf^! ω_Y ≅ ω_X`, and the tensor–Hom exchange at `N = ω_Y` then gives the
*Verdier-duality exchange*

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`,

natural in `M`. This file constructs it as a natural isomorphism of functors
`D(X_ét)ᵒᵖ ⥤ D(Y_ét)`, for every coefficient category in which the projection formula holds.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIso`
  (`thm-sf-verdier-exchange`, Step 1): `Rf^! ω_Y ≅ ω_X`, the mate of a composition isomorphism.
- `AlgebraicGeometry.Etale.verdierDualRightDerivedLowerShriekIso` (`thm-sf-verdier-exchange`):
  the natural isomorphism `𝔻_Y ∘ Rf_! ≅ Rf_* ∘ 𝔻_X`.
- `AlgebraicGeometry.Etale.verdierDualRightDerivedLowerShriekShiftIso`
  (`thm-sf-verdier-exchange`, shifts): `𝔻_Y (Rf_!(M⟦a⟧)) ≅ (Rf_* 𝔻_X M)⟦-a⟧`.

## Main statements

- `AlgebraicGeometry.Etale.verdierDualRightDerivedLowerShriekIso_hom_app`: the exchange is the
  inverse of the tensor–Hom exchange at `N = ω_Y` followed by `Rf_* RHom(M, Rf^! ω_Y ≅ ω_X)`;
  in particular its compatibility with changes of coefficients is that of the tensor–Hom
  exchange (`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv`)
  and of the mate `Rf^! ω_Y ≅ ω_X`.
- `AlgebraicGeometry.Etale.nonempty_verdierDualRightDerivedLowerShriekIso`
  (`thm-sf-verdier-exchange`): at finite coefficients, the natural isomorphism exists.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ S) [HasCompactification f]
  [HasCompactification aY] [HasCompactification (f ≫ aY)] [(R(f)_![A]).IsLeftAdjoint]
  [(R(aY)_![A]).IsLeftAdjoint] [(R(f ≫ aY)_![A]).IsLeftAdjoint]

/-- Blueprint `thm-sf-verdier-exchange`, Step 1: `Rf^! ω_Y ≅ ω_X`.

For a composition isomorphism `e : R(f ≫ a_Y)_! ≅ Rf_! ⋙ Ra_{Y!}`
(`sk-thm-sf-comp-composition`), the mate of `e` under the adjunctions `Rf_! ⊣ Rf^!` is an
isomorphism `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!` (`sk-lem-sf-mate`); evaluated at the unit `Λ_S` it
reads `Rf^! ω_Y ≅ ω_X`. -/
noncomputable def rightDerivedUpperShriekDualizingComplexIso
    (e : R(f ≫ aY)_![A] ≅ R(f)_![A] ⋙ R(aY)_![A]) :
    (R(f)^![A]).obj (dualizingComplex A aY) ≅ dualizingComplex A (f ≫ aY) :=
  (((rightDerivedUpperShriekAdjunction A (f ≫ aY)).ofNatIsoLeft e).rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction A f).comp
      (rightDerivedUpperShriekAdjunction A aY))).symm.app (𝟙_ _)

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- Blueprint `thm-sf-verdier-exchange`: Verdier-duality exchange.

Let `f : X ⟶ Y` and the structure morphism `a_Y : Y ⟶ S` admit compactifications, with
`a_X = f ≫ a_Y`, and assume the projection formula for `f` (axiom (A3) of `def-sf-datum`). For a
composition isomorphism `e : R(a_Y ∘ f)_! ≅ Ra_{Y!} ∘ Rf_!` there is an isomorphism

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`,

natural in `M ∈ D(X_ét)`. As in the blueprint it is the tensor–Hom exchange
`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`) at `N = ω_Y`, followed by the
mate `Rf^! ω_Y ≅ ω_X` of `e` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIso`).
The blueprint takes `M ∈ Dᵇctf(X, Λ)`; no finiteness of `M` is needed. -/
noncomputable def verdierDualRightDerivedLowerShriekIso [IsIso (projectionMap A f)]
    (e : R(f ≫ aY)_![A] ≅ R(f)_![A] ⋙ R(aY)_![A]) :
    (R(f)_![A]).op ⋙ verdierDual A aY ≅ verdierDual A (f ≫ aY) ⋙ R((f)_*[A]) :=
  (Functor.isoWhiskerRight (derivedHomRightDerivedLowerShriekIso A f)
      ((CategoryTheory.evaluation _ _).obj (dualizingComplex A aY))).symm ≪≫
    NatIso.ofComponents (fun M ↦ (R((f)_*[A])).mapIso
        (((RHom(X)[A]).obj M).mapIso (rightDerivedUpperShriekDualizingComplexIso A f aY e)))
      (fun {M M'} g ↦ by
        dsimp [verdierDual]
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        exact (((RHom(X)[A]).map g).naturality _).symm)

omit [HasSmallSiteSheafify A] in
/-- The component of the Verdier-duality exchange: the inverse of the tensor–Hom exchange at
`N = ω_Y`, followed by `Rf_* RHom(M, -)` of `Rf^! ω_Y ≅ ω_X`. -/
lemma verdierDualRightDerivedLowerShriekIso_hom_app [IsIso (projectionMap A f)]
    (e : R(f ≫ aY)_![A] ≅ R(f)_![A] ⋙ R(aY)_![A])
    (M : (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ) :
    (verdierDualRightDerivedLowerShriekIso A f aY e).hom.app M =
      ((derivedHomRightDerivedLowerShriekIso A f).inv.app M).app (dualizingComplex A aY) ≫
        (R((f)_*[A])).map (((RHom(X)[A]).obj M).map
          (rightDerivedUpperShriekDualizingComplexIso A f aY e).hom) :=
  rfl

/-- Blueprint `thm-sf-verdier-exchange`: Verdier-duality exchange, compatibility with shifts.

For every `M` and `a : ℤ`, `𝔻_Y (Rf_!(M⟦a⟧)) ≅ (Rf_* 𝔻_X M)⟦-a⟧`: the Verdier dual of the
commutation `Rf_!(M⟦a⟧) ≅ (Rf_! M)⟦a⟧`, then `RHom(N⟦a⟧, ω_Y) ≅ RHom(N, ω_Y)⟦-a⟧`
(`AlgebraicGeometry.Etale.derivedHomShiftIso`), then the shift of the exchange for `M`. -/
noncomputable def verdierDualRightDerivedLowerShriekShiftIso [IsIso (projectionMap A f)]
    (e : R(f ≫ aY)_![A] ≅ R(f)_![A] ⋙ R(aY)_![A])
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (a : ℤ) :
    (verdierDual A aY).obj (op ((R(f)_![A]).obj (M⟦a⟧))) ≅
      ((R((f)_*[A])).obj ((verdierDual A (f ≫ aY)).obj (op M)))⟦-a⟧ :=
  ((verdierDual A aY).mapIso (((R(f)_![A]).commShiftIso a).app M).op).symm ≪≫
    (derivedHomShiftIso A _ a).app (dualizingComplex A aY) ≪≫
      (((RHom(Y)[A]).obj (op ((R(f)_![A]).obj M))).commShiftIso (-a)).app _ ≪≫
        (shiftFunctor _ (-a)).mapIso ((verdierDualRightDerivedLowerShriekIso A f aY e).app (op M))

end General

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}} (f : X ⟶ Y)
  (aY : Y ⟶ S) [HasCompactification f] [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- Blueprint `thm-sf-verdier-exchange`: Verdier-duality exchange.

For `f : X ⟶ Y` separated of finite type over the structure morphism `a_Y : Y ⟶ S` (all of
`f`, `a_Y` and `a_X = f ≫ a_Y` admitting compactifications, which by Nagata holds for every
separated finite-type morphism over a quasi-compact quasi-separated base) and a finite
coefficient ring `Λ`, there is an isomorphism

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`,

natural in `M ∈ D(X_ét, Λ)`, with `ω_X = Ra_X^! Λ` and `ω_Y = Ra_Y^! Λ` formed with the
exceptional inverse image of `def-weil-exceptional-inverse-image` (no admissibility datum is
assumed). It is `AlgebraicGeometry.Etale.verdierDualRightDerivedLowerShriekIso` for the
composition isomorphism of `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`,
the projection formula holding at finite coefficients
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`). Its compatibility with shifts is
`AlgebraicGeometry.Etale.verdierDualRightDerivedLowerShriekShiftIso`, and its compatibility
with finite reduction and scalar extension is that of its two ingredients
(`AlgebraicGeometry.Etale.verdierDualRightDerivedLowerShriekIso_hom_app`,
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv`). -/
theorem nonempty_verdierDualRightDerivedLowerShriekIso :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).op ⋙ verdierDual _ aY ≅
      verdierDual _ (f ≫ aY) ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f aY
  have := isIso_projectionMap_of_finite Λ f
  exact ⟨verdierDualRightDerivedLowerShriekIso _ f aY e⟩

end Finite

end Etale

end AlgebraicGeometry
