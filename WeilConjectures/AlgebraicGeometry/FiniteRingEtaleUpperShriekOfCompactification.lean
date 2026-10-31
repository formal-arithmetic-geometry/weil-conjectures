/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingProperEtaleAdjoint
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Étale exceptional pullback along a compactification

Source: latest blueprint, sec-six-functors-basics, sk-prop-sf-existence, order 2550
(blueprint: def-sfb-finite-upper-shriek-compactification).

The proper part supplies a chosen right adjoint, followed by the levelwise exact inverse
image along the open part. Coefficients are finite rings, without a commutativity assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The exceptional pullback along the given compactification, with finite ring coefficients.
Source: latest blueprint, order 2550
(blueprint: def-sfb-finite-upper-shriek-compactification).

`c.obj.obj` is the underlying compactification; the boundary compactification retains
quasi-compactness of its open immersion. The first factor chooses the right adjoint of
proper derived pushforward using its existence theorem. The second is the derived functor
of the exact inverse image, hence applies inverse image levelwise without a resolution.
The adjunction determines the chosen first factor up to unique adjunction-compatible
isomorphism; no arbitrary object is chosen from an undetermined existence assertion. -/
noncomputable def finiteRingRightDerivedUpperShriekOfCompactification
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f) :
    DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  letI := finiteRing_isLeftAdjoint_rightDerivedLowerStar_of_isProper Λ c.obj.obj.g
  (lowerStar (ModuleCat.{u + 1} Λ) c.obj.obj.g).rightDerivedFunctor.rightAdjoint ⋙
    (upperStar (ModuleCat.{u + 1} Λ) c.obj.obj.i).mapDerivedCategory

end AlgebraicGeometry.Etale
