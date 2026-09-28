/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# The tensor product of sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)`. For sheaves of modules `M` and `N`
over `R`, the tensor product `M ⊗_R N` is the sheafification of the tensor product of the
underlying presheaves of modules (`PresheafOfModules.Monoidal`).

## Main definitions

- `SheafOfModules.tensorObj`: the tensor product `M ⊗_R N` of two sheaves of modules.
- `SheafOfModules.tensorHom`: the tensor product of two morphisms of sheaves of modules.
- `SheafOfModules.tensorFunctor`: the tensor product as a bifunctor.
- `SheafOfModules.leftUnitor`: the isomorphism `R ⊗_R M ≅ M`.
- `SheafOfModules.braiding`: the isomorphism `M ⊗_R N ≅ N ⊗_R M`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The sheafification functor for presheaves of modules over the underlying presheaf of rings
of a sheaf of commutative rings `R`. -/
noncomputable abbrev sheafificationCommRing :
    PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  PresheafOfModules.sheafification (𝟙 _)

variable {R}

/-- The tensor product `M ⊗_R N` of two sheaves of modules over a sheaf of commutative rings
`R`: the sheafification of the tensor product of the underlying presheaves of modules. -/
noncomputable def tensorObj
    (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  (sheafificationCommRing R).obj (PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val)

/-- The tensor product `f ⊗ g : M₁ ⊗_R M₃ ⟶ M₂ ⊗_R M₄` of two morphisms of sheaves of
modules. -/
noncomputable def tensorHom
    {M₁ M₂ M₃ M₄ : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) : tensorObj M₁ M₃ ⟶ tensorObj M₂ M₄ :=
  (sheafificationCommRing R).map (PresheafOfModules.Monoidal.tensorHom f.val g.val)

variable (R) in
/-- The tensor product of sheaves of modules over a sheaf of commutative rings `R`, as a
bifunctor. -/
noncomputable def tensorFunctor :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  forget _ ⋙ curriedTensor (PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) ⋙
    (Functor.whiskeringLeft _ _ _).obj (forget _) ⋙
      (Functor.whiskeringRight _ _ _).obj (sheafificationCommRing R)

@[simp]
lemma tensorFunctor_obj_obj
    (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ((tensorFunctor R).obj M).obj N = tensorObj M N :=
  rfl

variable (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- The left unitor `R ⊗_R M ≅ M`: the sheafification of the left unitor of presheaves of
modules, followed by the counit of the sheafification adjunction. -/
noncomputable def leftUnitor : tensorObj (unit _) M ≅ M :=
  (sheafificationCommRing R).mapIso 
    (MonoidalCategoryStruct.leftUnitor (C := PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit).app M

/-- The braiding `M ⊗_R N ≅ N ⊗_R M`: the sheafification of the braiding of presheaves of
modules. -/
noncomputable def braiding : tensorObj M N ≅ tensorObj N M :=
  (sheafificationCommRing R).mapIso 
    (BraidedCategory.braiding (C := PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) M.val N.val)

end SheafOfModules
