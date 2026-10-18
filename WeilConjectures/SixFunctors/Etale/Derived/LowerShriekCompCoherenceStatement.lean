/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-!
# The coherent composition law for `Rf_!`: the statement

The composition law `Rh_! ≅ Rf_! ⋙ Rg_!` for `h = f ≫ g` (`sk-thm-sf-comp-composition`),
compatible with the projection maps (`sk-prop-sf-pf-coherence`) and with compact-support base
change (`sk-thm-sf-package` (2)), as a proposition
`AlgebraicGeometry.Etale.RightDerivedLowerShriekCompCoherence`, and the theorem asserting it
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompCoherence`).

## Implementation notes

The compatibility with the projection maps is stated for a general coefficient category
(`AlgebraicGeometry.Etale.ProjectionCompCoherent`) and then specialised to `ModuleCat Λ`:
elaborating it directly at `ModuleCat Λ` unifies the projection maps against the monoidal
structure of the derived category and exhausts the memory.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product (see `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence`).
attribute [local instance high] SymmetricCategory.toBraidedCategory

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- Composition isomorphisms `E f g h w : Rh_! ≅ Rf_! ⋙ Rg_!` are *compatible with the projection
maps* (`sk-prop-sf-pf-coherence`) if for all composable `f`, `g` the projection maps of `f`, `g`
and `h = f ≫ g` compose through `E f g h w`.

It is stated for a general coefficient category: stated directly for `ModuleCat Λ`, elaborating
the projection maps against the monoidal structure is very expensive. -/
def ProjectionCompCoherent (E : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z),
    f ≫ g = h → ∀ [HasCompactification f] [HasCompactification g] [HasCompactification h],
      R(h)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification h],
    Adjunction.ProjectionCompCompatible
      (fun M N ↦ ((projectionMap A f).app M).app N)
      (fun M N ↦ ((projectionMap A g).app M).app N)
      (fun M N ↦ ((projectionMap A h).app M).app N)
      (fun N ↦ (leftDerivedUpperStarComp A f g h w.symm).hom.app N) (E f g h w)

end General

/-- The coherent composition law for `Rf_!` at finite coefficients: the statement of
`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso` (blueprints
`sk-thm-sf-comp-composition`, `sk-prop-sf-pf-coherence`, `sk-thm-sf-package` (2)). There are
composition isomorphisms `E f g h w : Rh_! ≅ Rf_! ⋙ Rg_!` compatible with the projection maps and
with the compact-support base change maps of pasted cartesian squares. -/
def RightDerivedLowerShriekCompCoherence : Prop :=
  ∃ E : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z), f ≫ g = h →
      ∀ [HasCompactification f] [HasCompactification g] [HasCompactification h],
      R(h)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ],
    ProjectionCompCoherent (ModuleCat.{u + 1} Λ) E ∧
    (∀ {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {f' : X' ⟶ Y'}
      {g' : Y' ⟶ Z'} {h' : X' ⟶ Z'} {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
      (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) (sqh : IsPullback a h' h c)
      (w : f ≫ g = h) (w' : f' ≫ g' = h') [HasCompactification f] [HasCompactification g]
      [HasCompactification h] [HasCompactification f'] [HasCompactification g']
      [HasCompactification h'] [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact h'],
      Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
        (rightDerivedLowerShriekBaseChangeMap Λ sqg) (rightDerivedLowerShriekBaseChangeMap Λ sqh)
        (E f g h w) (E f' g' h' w'))

/-- Blueprints `sk-thm-sf-comp-composition`, `sk-prop-sf-pf-coherence` and `sk-thm-sf-package`
(clause (2)): the composition law for `Rf_!` and its coherence with the projection formula and
with base change. This is the statement of
`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`, in a form whose elaboration is
cheap. -/
theorem rightDerivedLowerShriekCompCoherence : RightDerivedLowerShriekCompCoherence Λ :=
  sorry

end Etale

end AlgebraicGeometry
