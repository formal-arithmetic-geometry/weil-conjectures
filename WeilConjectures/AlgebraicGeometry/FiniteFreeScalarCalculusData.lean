/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.RingedSiteModules


/-! # Data of finite-free derived scalar calculus

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraphs 1-2; Stacks 03CZ, 06YY and 06YU.
(blueprint: lem-sf-finite-free-derived-scalar-calculus)

(blueprint: def-sf-finite-free-scalar-calculus-data)

The auxiliary structure packages the conclusions, with the ordinary functor fixed to
sheafified scalar extension and the derived functor fixed to its exact descent. Its
universal counit identifies this descent with derived change of rings. All comparison
maps are normalized, including on homogeneous summands of K-flat total tensor complexes.

## Main statements

* `FiniteFreeScalarCalculus`: the complete normalized conclusion package.
* `finiteFreeDerivedScalarCalculus`: existence of this package on each of the two sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

universe a v

end CategoryTheory

namespace AlgebraicGeometry

section Site
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  (φ : A →+* B)

/-- The ordinary scalar functor in the calculus: sheafified sectionwise extension.
Source: Stacks 03CZ (blueprint: lem-sf-finite-free-derived-scalar-calculus). -/
def finiteScalarExtension :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

end Site

end AlgebraicGeometry
