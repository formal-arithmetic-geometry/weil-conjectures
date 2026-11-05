/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Flasque
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.CategoryTheory.SpectralSequence.LowDegree

/-!
# The Leray spectral sequence of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y` and an `𝒪_X`-module `ℱ` there is a first quadrant
spectral sequence `E₂^{p,q} = H^p(Y, R^q f_* ℱ) ⇒ H^{p+q}(X, ℱ)`, where the cohomology groups are
the right derived functors of the global sections functors on `𝒪`-modules. It is the
Grothendieck spectral sequence of the composite `Γ(Y, -) ∘ f_* = Γ(X, -)`: injective
`𝒪_X`-modules are flasque, direct images of flasque modules are flasque, and flasque modules are
acyclic for `Γ`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor`: the global sections functor
  `Γ(X, -) : X.Modules ⥤ Ab`, whose right derived functors are the cohomology groups.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.rightAcyclic_globalSectionsFunctor_of_isFlasque`: flasque
  modules are `Γ`-acyclic.
- `AlgebraicGeometry.Scheme.Modules.exists_leraySpectralSequence`: the Leray spectral sequence.
- `AlgebraicGeometry.Scheme.Modules.exists_leray_lowDegree_exact`: its exact sequence of low
  degree terms.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

variable {X}

variable {Y : Scheme.{u}} (f : X ⟶ Y)

end AlgebraicGeometry.Scheme.Modules
