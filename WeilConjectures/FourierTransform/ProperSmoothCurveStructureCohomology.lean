/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Structure-sheaf cohomology in a smooth proper curve family

Source: Stacks Project, `curves.tex`, Tag 0GKA (lemma-genus-in-nodal-family-of-curves),
lines 5018--5060; specialization to smooth proper geometrically connected curves
(blueprint: lem-fd-proper-smooth-curve-structure-cohomology).

The statement uses the small Zariski site of a scheme, the associated sheaves of modules
and their bounded-below derived categories.  The proof follows the proper-flat global
sections theorem, perfect derived base change, fibre cohomology vanishing above the
one-dimensional fibre, and the finite-free residue-field model; the resulting two-term
model has zero differential because its degree-zero structure map is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

/-- For a proper smooth family of geometrically connected curves, the structure-sheaf
cohomology has the expected degree-zero, vanishing, and finite locally free conclusions.
Source: Stacks Project, `curves.tex`, Tag 0GKA (lemma-genus-in-nodal-family-of-curves),
lines 5018--5060 (blueprint: lem-fd-proper-smooth-curve-structure-cohomology).

The fibres are nonempty and geometrically connected (`GeometricallyConnected f`, whose
`ConnectedSpace` includes nonemptiness) and of pure dimension one: a smooth connected
fibre is equidimensional, so this is `topologicalKrullDim (f.fiber s) = 1`.

Proof: (1) smoothness gives flatness and local finite presentation, properness gives
quasi-compactness and quasi-separatedness, hence finite presentation; smooth fibres are
geometrically reduced, so the proper-flat global sections theorem (Stacks 0E0L) makes the
structure map `𝒪_S → f_*𝒪_X` an isomorphism, universally under base change.
(2) Put `K = Rf_*𝒪_X`; by perfect proper base change (Stacks 0B91) `K` is perfect and
`L i_s^* K ≅ R(f_s)_*𝒪_{X_s}` for every residue-field point `s`.
(3) Each fibre is proper over `κ(s)`, hence Noetherian of dimension one, so its structure
sheaf has no cohomology in degrees at least two (Stacks 02UZ), and `H^0 = κ(s)` by (1).
(4) The minimal finite-free model (Stacks 0BCD) over an affine neighbourhood `U` of `s` is
`[𝒪_U → 𝒪_U^g]` in degrees `0, 1`, so `R^q f_*𝒪_X` vanishes near `s` for `q ≥ 2`.
(5) The degree-zero base-change isomorphism forces the image `b` of `1` in `C^0` to be
invertible at `s`; after shrinking, `d(b) = b d(1) = 0` gives `d = 0`, including over
nonreduced bases, so `R^1 f_*𝒪_X` is finite locally free.
-/
theorem properSmoothCurve_structureSheaf_cohomology
    {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    [HasDerivedCategory.{u} S.Modules] [HasDerivedCategory.{u} X.Modules]
    [EnoughInjectives X.Modules]
    :
    IsIso ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
      (SheafOfModules.unit S.ringCatSheaf)) ∧
      (∀ q : ℤ, 2 ≤ q →
        IsZero ((DerivedCategory.Plus.homologyFunctor S.Modules q).obj
          ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
              (SheafOfModules.unit X.ringCatSheaf))))) ∧
      ((DerivedCategory.Plus.homologyFunctor S.Modules 1).obj
          ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
              (SheafOfModules.unit X.ringCatSheaf)))).IsFiniteLocallyFree := by
  sorry

end AlgebraicGeometry
