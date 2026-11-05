/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# Module objects as cokernels of free module objects

Let `C` be an abelian monoidal category and `A` a monoid object of `C` such that `A ⊗ -` is right
exact. Every `A`-module object `M` is the cokernel of a morphism of free `A`-modules
`A ⊗ K ⟶ A ⊗ M`, the counit `A ⊗ M ⟶ M` of the free-forgetful adjunction being an epimorphism
(`CategoryTheory.Mod.isColimitCounitCokernelCofork`). Consequently a natural transformation
between right exact functors on `Mod C A` is an isomorphism as soon as it is one on free modules
(`CategoryTheory.Mod.isIso_app_of_isIso_app_free`).
-/

@[expose] public section

namespace CategoryTheory.Mod

open MonoidalCategory MonObj Limits

variable {C : Type*} [Category* C] [MonoidalCategory C] (A : C) [MonObj A] [Abelian C]
  [MonoidalPreadditive C] [PreservesFiniteColimits (tensorLeft A)]

/-- The counit `A ⊗ M ⟶ M` of the free-forgetful adjunction is an epimorphism: its underlying
morphism is split by the unit. -/
instance epi_freeForgetAdjunction_counit_app (M : Mod C A) :
    Epi ((freeForgetAdjunction A).counit.app M) :=
  have : IsSplitEpi ((forget A).map ((freeForgetAdjunction A).counit.app M)) :=
    ⟨⟨(freeForgetAdjunction A).unit.app ((forget A).obj M),
      (freeForgetAdjunction A).right_triangle_components M⟩⟩
  (forget A).epi_of_epi_map inferInstance

end CategoryTheory.Mod
