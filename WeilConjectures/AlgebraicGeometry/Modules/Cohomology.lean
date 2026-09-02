/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.SheafOfModules
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# Coherent cohomology of a scheme over a base ring

Let `R` be a commutative ring and `f : X ⟶ Spec R` a morphism of schemes. Global sections of
an `𝒪_X`-module form a module over `Γ(X, ⊤)`, hence an `R`-module by restriction of scalars
along `f`. This file defines the resulting functor and its right derived functors, which are
the cohomology groups `Hⁱ(X, ℱ)` of an `𝒪_X`-module `ℱ`, regarded as `R`-modules.

Equivalently, these are the higher direct images of `ℱ` along `f`, evaluated on the base.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor f`: the functor
  `X.Modules ⥤ ModuleCat R` sending an `𝒪_X`-module to its `R`-module of global sections.
- `AlgebraicGeometry.Scheme.Modules.cohomology f i`: the `i`-th right derived functor of the
  above, that is, `ℱ ↦ Hⁱ(X, ℱ)` as an `R`-module.
- `AlgebraicGeometry.Scheme.Modules.cohomologyZeroIso f`: the identification
  `H⁰(X, -) ≅ Γ(X, -)`.

That the right derived functors exist rests on `X.Modules` having enough injectives, which is
recorded in `WeilConjectures.CategoryTheory.GrothendieckAbelian.SheafOfModules`.  The proof of
the instance there is a `sorry`, so `#print axioms` reports `sorryAx` on `cohomology` and on
everything built from it.

## Blueprint

`cohomology` is the formalised form of the cohomology groups `Hⁱ(X, ℱ)` used by
`def:pc-euler-characteristic`; it implements `def:pc-derived-direct-image` in the special case
of an affine base, evaluated on the base.  The general higher direct image `Rⁱf_*` along an
arbitrary morphism is not formalised here.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

namespace Scheme.Modules

/-- The global sections of an `𝒪_X`-module, as a module over the base ring `R` of a morphism
`f : X ⟶ Spec R`: evaluation on the top open subset followed by restriction of scalars along
`R →+* Γ(X, ⊤)`. -/
noncomputable def globalSectionsFunctor (f : X ⟶ Spec R) : X.Modules ⥤ ModuleCat.{u} R :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars f.baseRingHom

instance (f : X ⟶ Spec R) : (globalSectionsFunctor f).Additive :=
  inferInstanceAs (SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars f.baseRingHom).Additive

noncomputable instance (f : X ⟶ Spec R) : PreservesFiniteLimits (globalSectionsFunctor f) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars f.baseRingHom))

/-- The cohomology `Hⁱ(X, -)` of a scheme `X` over `Spec R`, with values in `R`-modules: the
`i`-th right derived functor of global sections. -/
noncomputable def cohomology (f : X ⟶ Spec R) (i : ℕ) : X.Modules ⥤ ModuleCat.{u} R :=
  (globalSectionsFunctor f).rightDerived i

/-- Degree zero cohomology is global sections. -/
noncomputable def cohomologyZeroIso (f : X ⟶ Spec R) :
    cohomology f 0 ≅ globalSectionsFunctor f :=
  (globalSectionsFunctor f).rightDerivedZeroIsoSelf

end Scheme.Modules

end AlgebraicGeometry
