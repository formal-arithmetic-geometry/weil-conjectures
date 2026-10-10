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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.ContinuousMap

/-!

# The derived tensor product of module objects over `C(-, T)`

Let `T` be a commutative topological ring and `X` a scheme. The category `Mod_{A_X(T)}` of
module objects over the coefficient ring object `A_X(T) = C(-, T)` of abelian pro-étale
sheaves on `X` is a closed symmetric monoidal Grothendieck abelian category for the relative
tensor product `⊗_{A_X(T)}` (`WeilConjectures.CategoryTheory.ModuleObjects`), so its derived
category `D(Mod_{A_X(T)})` carries the *derived tensor product* `- ⊗ᴸ_{A_X(T)} -`, the total
left derived functor of `⊗_{A_X(T)}` in two variables, computed on K-flat resolutions
(`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`).

## Main definitions

- `AlgebraicGeometry.ProEtale.ContinuousMapRing.derivedTensor` : the derived tensor product
  `- ⊗ᴸ_{A_X(T)} - : D(Mod_{A_X(T)}) ⥤ D(Mod_{A_X(T)}) ⥤ D(Mod_{A_X(T)})`, with scoped notation
  `-⊗ᴸ-(X)⟦T⟧`.

## Main results

- `AlgebraicGeometry.ProEtale.ContinuousMapRing.isLeftDerivedFunctor₂_derivedTensor` : the
  derived tensor product is the total left derived functor of the relative tensor product of
  module objects, in two variables.

- `AlgebraicGeometry.ProEtale.ContinuousMapRing.laxMonoidal_Q` : the localization functor
  `Q : C(Mod_{A_X(T)}) ⥤ D(Mod_{A_X(T)})` is lax monoidal.

## Implementation notes

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`. The monoidal structure
on `D(Mod_{A_X(T)})` is the instance `Mod.derivedMonoidalCategory`, which rests on the sorried
inputs of `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` and
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`; the *type* of
`derivedTensor` does not mention it.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] (X : Scheme.{u})

/-- The derived tensor product
`- ⊗ᴸ_{A_X(T)} - : D(Mod_{A_X(T)}) ⥤ D(Mod_{A_X(T)}) ⥤ D(Mod_{A_X(T)})` on the unbounded derived
category of module objects over the coefficient ring object `A_X(T)`: the tensor product of the
monoidal structure on `D(Mod_{A_X(T)})` obtained from the K-flat left derivability structure. -/
@[implicit_reducible]
noncomputable def derivedTensor :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (continuousMapRingObj T X)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (continuousMapRingObj T X)) :=
  curriedTensor _

@[inherit_doc derivedTensor]
scoped notation "-⊗ᴸ-(" X ")⟦" T "⟧" => derivedTensor T X

noncomputable instance laxMonoidal_Q :
    (DerivedCategory.Q (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X))).LaxMonoidal :=
  Mod.laxMonoidalQ

noncomputable instance laxMonoidal_Qh :
    (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X))).LaxMonoidal :=
  inferInstance

/-- The derived tensor product of module objects over `A_X(T)` is the total left derived
functor of the relative tensor product `⊗_{A_X(T)}` of complexes of module objects, in two
variables. -/
instance isLeftDerivedFunctor₂_derivedTensor :
    -⊗ᴸ-(X)⟦T⟧.IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (continuousMapRingObj T X)) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (continuousMapRingObj T X)) (ComplexShape.up ℤ)) :=
  Mod.isLeftDerivedFunctor₂_curriedTensor

end AlgebraicGeometry.ProEtale.ContinuousMapRing
