/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import Submission.WeilConjectures.Algebra.Homology.ExtWithAction
public import Submission.WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ResolutionScalarAction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Cohomology of derived global sections

For a morphism of schemes `f : X ⟶ S` and an `𝒪_X`-module `ℱ`, the derived global sections
`RΓ(X, ℱ)` are an object of `D(Γ(S, ⊤))`, where `Γ(S, ⊤)` acts through `f^♯`
(`AlgebraicGeometry.Scheme.Modules.derivedGlobalSectionsOver`). We identify its cohomology in
degree `n` with the sheaf cohomology `H^n(X, ℱ) = Ext^n(ℤ, ℱ)` of the underlying abelian sheaf,
as `Γ(S, ⊤)`-modules, where `Γ(S, ⊤)` acts on the `Ext`-group through multiplication by global
functions (`CategoryTheory.Abelian.Ext.WithAction`).

The additive comparison is `AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv`
(injective `𝒪_X`-modules are acyclic for `Γ` on abelian sheaves, Stacks 03FD). It is natural in
`ℱ`, and on both sides multiplication by `a ∈ Γ(X, ⊤)` is induced by the endomorphism `a • -`
of `ℱ` (`AlgebraicGeometry.Scheme.Modules.moduleCohomology_map_smulHom`), so it is linear.

We also record that extension of scalars along a flat ring map is exact, so that it induces a
functor on derived categories commuting with cohomology.
-/

@[expose] public section

universe w wA u

open CategoryTheory Limits TopologicalSpace Opposite

/-- Extension of scalars preserves finite colimits, as a left adjoint. -/
instance ModuleCat.preservesFiniteColimits_extendScalars {R S : Type u} [CommRing R]
    [CommRing S] (φ : R →+* S) : PreservesFiniteColimits (extendScalars.{u, u, u} φ) :=
  have := (extendRestrictScalarsAdj.{u, u, u} φ).leftAdjoint_preservesColimits
  inferInstance

namespace AlgebraicGeometry

/-- Extension of scalars along the map on global functions of a flat morphism of affine
schemes is exact. -/
instance {T S : Scheme.{u}} [IsAffine S] [IsAffine T] (g : T ⟶ S) [Flat g] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g.appTop.hom) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat g.flat_appTop

namespace Scheme.Modules

open CategoryTheory.Abelian.Ext

variable {X : Scheme.{u}}

variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
  [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- The derived global sections `RΓ(X, ℱ)` of an `𝒪_X`-module `ℱ`, as an object of `D(A)` for
`A = Γ(S, ⊤)` acting through `f^♯`. -/
noncomputable abbrev derivedGlobalSectionsOver {S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) :
    DerivedCategory (ModuleCat.{u} Γ(S, ⊤)) :=
  (schemeGlobalScalarRestriction f).obj
    ((schemeDerivedGlobalSections X).obj ((DerivedCategory.singleFunctor _ 0).obj ℱ))

end Scheme.Modules

end AlgebraicGeometry
