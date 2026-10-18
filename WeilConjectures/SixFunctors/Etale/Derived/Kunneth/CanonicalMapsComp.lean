/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CanonicalMapsSupport

/-!

# Composition of the canonical maps of `Rf^!`, given a coherent composition law

The composition law `Rh_! ≅ Rf_! ⋙ Rg_!` for `h = f ≫ g`, compatible with the projection maps
(`sk-prop-sf-pf-coherence`) and with compact-support base change (`sk-thm-sf-package` (2)), is
recorded here as a hypothesis, `AlgebraicGeometry.Etale.RightDerivedLowerShriekCompCoherence`;
it is the statement of `AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`. From it
the canonical maps of `R^!` — the base change map and the tensor map `θ` — compose:

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff_of_coherence`:
  the base change map of `R(f ≫ g)^!` is, up to the composition isomorphisms, the composite of
  those of `Rf^!` and `Rg^!`;
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_comp_iff`: `θ_{f ≫ g, K}` is an
  isomorphism if and only if `Rf^! θ_{g, K}` is one, as soon as the tensor map of `f` at
  `(ω_g, Lg^* K)` is an isomorphism.
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

/-- The coherent composition law for `Rf_!` at finite coefficients: the statement of
`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso` (blueprints
`sk-thm-sf-comp-composition`, `sk-prop-sf-pf-coherence`, `sk-thm-sf-package` (2)). There are
composition isomorphisms `E f g h w : Rh_! ≅ Rf_! ⋙ Rg_!` compatible with the projection maps and
with the compact-support base change maps of pasted cartesian squares. -/
def RightDerivedLowerShriekCompCoherence : Prop :=
  ∃ E : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z), f ≫ g = h →
      ∀ [HasCompactification f] [HasCompactification g] [HasCompactification h],
      R(h)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ],
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
      [HasCompactification f] [HasCompactification g] [HasCompactification h],
      Adjunction.ProjectionCompCompatible
        (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
        (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) g).app M).app N)
        (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) h).app M).app N)
        (fun N ↦ (leftDerivedUpperStarComp _ f g h w.symm).hom.app N) (E f g h w)) ∧
    (∀ {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {f' : X' ⟶ Y'}
      {g' : Y' ⟶ Z'} {h' : X' ⟶ Z'} {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
      (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) (sqh : IsPullback a h' h c)
      (w : f ≫ g = h) (w' : f' ≫ g' = h') [HasCompactification f] [HasCompactification g]
      [HasCompactification h] [HasCompactification f'] [HasCompactification g']
      [HasCompactification h'] [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact h'],
      Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
        (rightDerivedLowerShriekBaseChangeMap Λ sqg) (rightDerivedLowerShriekBaseChangeMap Λ sqh)
        (E f g h w) (E f' g' h' w'))

variable {Λ}

end Etale

end AlgebraicGeometry
