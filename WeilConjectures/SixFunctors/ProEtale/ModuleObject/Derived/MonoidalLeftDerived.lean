/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComp

/-!
# The tensor comparison of the derived pullback is the generic one

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The pullback
`f^*` of module objects over `Λ` is exact, strong monoidal, a left adjoint, and preserves flat
objects (`ProEtale.CondensedRing.preservesFlat_upperStar`). Its left derived functor
`Lf^*` therefore carries the generic tensor comparison
`Functor.leftDerivedTensorComparison : Lf^*(K ⊗ᴸ M) ⟶ Lf^* K ⊗ᴸ Lf^* M`. This file shows that it
is the comparison `ProEtale.CondensedRing.leftDerivedUpperStarTensor` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`
(`ProEtale.CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison`): both are
characterized by their compatibility with the counits of the left derived functors.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of module objects preserves flat objects: it preserves K-flat complexes, and an
object is flat if and only if it is K-flat as a complex concentrated in degree `0`. -/
instance preservesFlat_upperStar : ((f)^*⟦Λ⟧).PreservesFlat := sorry

/-- The tensor comparison `Lf^*(K ⊗ᴸ M) ⟶ Lf^* K ⊗ᴸ Lf^* M` of the derived pullback of module
objects is the generic tensor comparison of the left derived functor of the strong monoidal
functor `f^*`. -/
theorem leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison :
    leftDerivedUpperStarTensor Λ f = ((f)^*⟦Λ⟧).leftDerivedTensorComparison := sorry

end AlgebraicGeometry.ProEtale.CondensedRing
