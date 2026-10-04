/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Notation for the right derived functor on the bounded below derived category

We introduce the notation `R+(F)` for
`CategoryTheory.Functor.rightDerivedFunctorPlus F`, the right derived functor
`DerivedCategory.Plus C ⥤ DerivedCategory.Plus D` of an additive functor `F : C ⥤ D`
between abelian categories, where `C` has enough injectives.

We also record that the right derived functor of `F` sends an injective object `I` placed
in a single degree `n` to `F.obj I` placed in degree `n`
(`CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleFunctorIso`): an injective object
is its own injective resolution.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

namespace Functor

@[inherit_doc rightDerivedFunctorPlus]
scoped notation "R+(" F ")" => rightDerivedFunctorPlus F

variable {C₀ C D : Type*} [Category* C₀] [Category* C] [Category* D] [Preadditive C₀]
  [HasZeroObject C₀] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]

/-- For an additive functor `G : C₀ ⥤ D`, the image in `DerivedCategory.Plus D` of the
single complex `X[n]` under `G.mapHomotopyCategoryPlus` is the single complex `(G.obj X)[n]`. -/
noncomputable def mapHomotopyCategoryPlusSingleFunctorQhObjIso (G : C₀ ⥤ D) [G.Additive]
    (n : ℤ) (X : C₀) :
    DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.singleFunctor C₀ n).obj X)) ≅
      (DerivedCategory.Plus.singleFunctor D n).obj (G.obj X) :=
  DerivedCategory.Plus.ι.preimageIso
    (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex G _ n).app X))

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The right derived functor of `F` sends an injective object `I` placed in degree `n` to
`F.obj I` placed in degree `n`: the single complex `I[n]` is a bounded below complex of
injective objects, on which the unit of the right derived functor is an isomorphism. -/
noncomputable def rightDerivedFunctorPlusObjSingleFunctorIso (n : ℤ) (I : C) [Injective I] :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C n).obj I) ≅
      (DerivedCategory.Plus.singleFunctor D n).obj (F.obj I) :=
  F.rightDerivedFunctorPlus.mapIso (mapHomotopyCategoryPlusSingleFunctorQhObjIso
      (InjectiveObject.ι C) n ⟨I, inferInstance⟩).symm ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.singleFunctor (InjectiveObject C) n).obj
        ⟨I, inferInstance⟩)))).symm ≪≫
    (mapHomotopyCategoryPlusSingleFunctorQhObjIso (InjectiveObject.ι C ⋙ F) n
      ⟨I, inferInstance⟩ :)

end Functor

end CategoryTheory
