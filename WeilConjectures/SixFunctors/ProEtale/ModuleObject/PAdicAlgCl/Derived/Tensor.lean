/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Basic

/-!

# The derived tensor product of module objects over `ℚ̄_ℓ`

Let `ℓ` be a prime and `X` a scheme. The category `Mod_{ℚ̄_ℓ,X}` of
module objects over the coefficient ring object `ℚ̄_ℓ,X` of abelian pro-étale
sheaves on `X` is a closed symmetric monoidal Grothendieck abelian category for the relative
tensor product `⊗_{ℚ̄_ℓ,X}` (`WeilConjectures.CategoryTheory.ModuleObjects`), so its derived
category `D(Mod_{ℚ̄_ℓ,X})` carries the *derived tensor product* `- ⊗ᴸ_{ℚ̄_ℓ,X} -`, the total
left derived functor of `⊗_{ℚ̄_ℓ,X}` in two variables, computed on K-flat resolutions
(`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`).

## Main definitions

- `AlgebraicGeometry.ProEtale.PadicAlgClRing.derivedTensor` : the derived tensor product
  `- ⊗ᴸ_{ℚ̄_ℓ,X} - : D(Mod_{ℚ̄_ℓ,X}) ⥤ D(Mod_{ℚ̄_ℓ,X}) ⥤ D(Mod_{ℚ̄_ℓ,X})`, with scoped notation
  `-⊗ᴸ-(X)⟦ℚ̄_ℓ⟧`.

## Main results

- `AlgebraicGeometry.ProEtale.PadicAlgClRing.isLeftDerivedFunctor₂_derivedTensor` : the
  derived tensor product is the total left derived functor of the relative tensor product of
  module objects, in two variables.

- `AlgebraicGeometry.ProEtale.PadicAlgClRing.laxMonoidal_Q` : the localization functor
  `Q : C(Mod_{ℚ̄_ℓ,X}) ⥤ D(Mod_{ℚ̄_ℓ,X})` is lax monoidal.

## Implementation notes

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`. The monoidal structure
on `D(Mod_{ℚ̄_ℓ,X})` is the instance `Mod.derivedMonoidalCategory`, which rests on the sorried
inputs of `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` and
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`; the *type* of
`derivedTensor` does not mention it.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})

/-- The derived tensor product
`- ⊗ᴸ_{ℚ̄_ℓ,X} - : D(Mod_{ℚ̄_ℓ,X}) ⥤ D(Mod_{ℚ̄_ℓ,X}) ⥤ D(Mod_{ℚ̄_ℓ,X})` on the unbounded derived
category of module objects over the coefficient ring object `ℚ̄_ℓ,X`: the tensor product of the
monoidal structure on `D(Mod_{ℚ̄_ℓ,X})` obtained from the K-flat left derivability structure. -/
@[implicit_reducible]
noncomputable def derivedTensor :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicAlgClSheaf X ℓ)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicAlgClSheaf X ℓ)) :=
  curriedTensor _

@[inherit_doc derivedTensor]
scoped notation "-⊗ᴸ-(" X ")⟦ℚ̄_" ℓ "⟧" => derivedTensor ℓ X

noncomputable instance laxMonoidal_Q :
    (DerivedCategory.Q (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))).LaxMonoidal :=
  Mod.laxMonoidalQ

noncomputable instance laxMonoidal_Qh :
    (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))).LaxMonoidal :=
  inferInstance

/-- The derived tensor product of module objects over `ℚ̄_ℓ,X` is the total left derived
functor of the relative tensor product `⊗_{ℚ̄_ℓ,X}` of complexes of module objects, in two
variables. -/
instance isLeftDerivedFunctor₂_derivedTensor :
    -⊗ᴸ-(X)⟦ℚ̄_ℓ⟧.IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicAlgClSheaf X ℓ)) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicAlgClSheaf X ℓ)) (ComplexShape.up ℤ)) :=
  Mod.isLeftDerivedFunctor₂_curriedTensor

end AlgebraicGeometry.ProEtale.PadicAlgClRing
