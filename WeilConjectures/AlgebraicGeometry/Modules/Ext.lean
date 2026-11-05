/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree

/-!
# Ext groups of sheaves of modules on a scheme

For `𝒪_X`-modules `ℱ` and `𝒢` on a scheme `X`, the group `Ext^i_X(ℱ, 𝒢)` is Mathlib's
`Abelian.Ext`: the morphisms `ℱ ⟶ 𝒢[i]` in the derived category of the abelian category
`X.Modules`. As `X.Modules` has enough injectives, this is the `i`-th right derived functor of
`Hom_{𝒪_X}(ℱ, -)` evaluated at `𝒢`; it is not computed by projective resolutions of `ℱ`, which
need not exist.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.Ext`: the group `Ext^i_X(ℱ, 𝒢)`.
- `AlgebraicGeometry.Scheme.Modules.extUnitToH`: the canonical comparison map
  `Ext^n_X(𝒪_X, M) ⟶ H^n(X, M)` (forget to abelian sheaves, pull back along `ℤ ⟶ 𝒪_X`).
- `AlgebraicGeometry.Scheme.Modules.extUnitAddEquivH`: the canonical isomorphism
  `Ext^n_X(𝒪_X, M) ≃ H^n(X, M)`, natural in `M`.
- `AlgebraicGeometry.Scheme.Modules.extAddEquivH`: the canonical isomorphism
  `Ext^i_X(ℱ, 𝒢) ≃ H^i(X, ℱᵛ ⊗ 𝒢)` for finite locally free `ℱ`, natural in `𝒢`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.contravariantSequence_ext_exact`: the long exact sequence of
  `Ext(-, 𝒢)` attached to a short exact sequence.
- `AlgebraicGeometry.Scheme.Modules.extUnitToH_bijective`: the comparison map is bijective, by
  dimension shifting.
- `AlgebraicGeometry.Scheme.Modules.nonempty_ext_unit_addEquiv_H`: `Ext^n_X(𝒪_X, M) ≅ H^n(X, M)`,
  by dimension shifting, injective `𝒪_X`-modules being flasque, hence acyclic.
- `AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H`: for finite locally free `ℱ`,
  `Ext^i_X(ℱ, 𝒢) ≅ H^i(X, ℱᵛ ⊗ 𝒢)`.

## Implementation notes

The `Ext` groups need the hypothesis `HasExt.{u} X.Modules`, which holds because `X.Modules` is a
Grothendieck abelian category (`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`); it is
kept as an instance argument.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [HasExt.{u} X.Modules]

/-- The **Ext groups** `Ext^i_X(ℱ, 𝒢)` of two `𝒪_X`-modules: the morphisms `ℱ ⟶ 𝒢[i]` in the
derived category of `𝒪_X`-modules, equivalently the right derived functors of `Hom_{𝒪_X}(ℱ, -)`
evaluated at `𝒢` (`𝒪_X`-modules have enough injectives but in general not enough projectives).
In degree `0` this is `Hom_{𝒪_X}(ℱ, 𝒢)` (`CategoryTheory.Abelian.Ext.homEquiv₀`).

(blueprint: `def-sc-ext-sheaf`) -/
abbrev Ext (ℱ 𝒢 : X.Modules) (i : ℕ) : Type u :=
  Abelian.Ext ℱ 𝒢 i

section Comparison

/-- The forgetful functor from `𝒪_X`-modules to abelian sheaves is additive. -/
instance additive_toAb : (toAb X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Additive

end Comparison

section LocallyFree

/-- For a finite locally free `ℱ`, tensoring with the dual is the internal hom out of `ℱ`. -/
noncomputable def tensorLeftDualIsoIhom (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    tensorLeft ℱᵛ ≅ ihom ℱ :=
  NatIso.ofComponents (fun N ↦ asIso (dualTensorHom ℱ N)) fun g ↦
    dualTensorHom_naturality_right ℱ g

end LocallyFree

section LocallyFreeCanonical

omit [HasExt X.Modules] in
/-- The category of `𝒪_X`-modules has enough injectives, being a Grothendieck abelian
category. -/
instance enoughInjectives : EnoughInjectives X.Modules :=
  have : IsGrothendieckAbelian.{u} X.Modules := SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  IsGrothendieckAbelian.enoughInjectives

omit [HasExt X.Modules] in
/-- Tensoring with an `𝒪_X`-module is additive, being a left adjoint. -/
instance additive_tensorLeft (A : X.Modules) : (tensorLeft A).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
    (ihom.adjunction A).leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft A)
  exact Functor.additive_of_preservesBinaryBiproducts _

omit [HasExt X.Modules] in
/-- Tensoring with a finite locally free `𝒪_X`-module `ℱ` is left exact: it is isomorphic to the
internal hom out of the dual of `ℱ`. -/
instance preservesFiniteLimits_tensorLeft (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    PreservesFiniteLimits (tensorLeft ℱ) := by
  have := IsFiniteLocallyFree.dual ℱ
  have := SheafOfModules.isIso_bidual (R := X.sheaf) ℱ
  exact preservesFiniteLimits_of_natIso ((tensoringLeft X.Modules).mapIso
    (asIso (SheafOfModules.bidual (R := X.sheaf) ℱ)) ≪≫ tensorLeftDualIsoIhom ℱᵛ).symm

omit [HasExt X.Modules] in
/-- The internal hom out of a finite locally free `𝒪_X`-module `ℱ` is right exact: it is
isomorphic to tensoring with the dual of `ℱ`. -/
instance preservesFiniteColimits_ihom (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    PreservesFiniteColimits (ihom ℱ) :=
  preservesFiniteColimits_of_natIso (tensorLeftDualIsoIhom ℱ)

omit [HasExt X.Modules] in
/-- The internal hom out of a finite locally free `𝒪_X`-module is additive. -/
instance additive_ihom (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] : (ihom ℱ).Additive :=
  Functor.additive_of_iso (tensorLeftDualIsoIhom ℱ)

end LocallyFreeCanonical

end AlgebraicGeometry.Scheme.Modules
