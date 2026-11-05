/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceConstruction
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Presheaf extension along the element projection

Source: Stacks Project, Modules on Sites, Tags 04IE and 03DJ
(blueprint: lem-weil-pbc-element-presheaf-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits DirectSum Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

@[no_expose] private noncomputable def rawSumFunctor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) :
    PresheafOfModules.{u} (elementRing R A).obj ⥤ PresheafOfModules.{u} R.obj :=
  Adjunction.leftAdjointOfEquiv (fun L M ↦ sumHomEquiv R A L M)
    (by intro L M N g f; ext e x; rfl)

@[no_expose] private noncomputable def rawSumAdjunction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) :
    rawSumFunctor R A ⊣ PresheafOfModules.pushforward
      (F := elementProjection A) (𝟙 (elementRing R A).obj) :=
  Adjunction.adjunctionOfEquivLeft (fun L M ↦ sumHomEquiv R A L M)
    (by intro L M N g f; ext e x; rfl)

open Classical in
@[no_expose] private noncomputable def rawSumEvaluationIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) (U : Cᵒᵖ) :
    fibreDiagram R A U ⋙ colim ≅
      rawSumFunctor R A ⋙ PresheafOfModules.evaluation R.obj U :=
  NatIso.ofComponents (fun L ↦ by
    exact ModuleCat.coprodIsoDirectSum
      (fun s : A.obj.obj U ↦ (show ModuleCat (R.obj.obj U) from L.obj (elementObj A U s)))) (by
      intro L N f
      apply Sigma.hom_ext
      intro s
      dsimp only [Functor.comp_map, Functor.comp_obj, fibreDiagram, colim_map]
      rw [ι_colimMap_assoc]
      erw [ModuleCat.ι_coprodIsoDirectSum_hom]
      rw [← Category.assoc]
      erw [ModuleCat.ι_coprodIsoDirectSum_hom]
      ext x
      change _ = ((rawSumFunctor R A).map f).app U
        (DirectSum.lof (R.obj.obj U) (A.obj.obj U)
          (fun t ↦ (L.obj (elementObj A U t) : Type u)) s x)
      rw [rawSumFunctor_map_lof]
      rfl)

end CategoryTheory
end
