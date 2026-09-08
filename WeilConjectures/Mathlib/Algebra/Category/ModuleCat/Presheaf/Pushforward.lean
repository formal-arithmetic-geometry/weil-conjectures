/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal

/-!
# The pushforward of presheaves of modules is lax monoidal

Let `R` and `R'` be presheaves of commutative rings on a category `C`. For a morphism
`α : R ⋙ forget₂ _ _ ⟶ R' ⋙ forget₂ _ _` of the underlying presheaves of rings, we
show that the restriction of scalars functor
`PresheafOfModules.restrictScalars α : PresheafOfModules (R' ⋙ forget₂ _ _) ⥤
PresheafOfModules (R ⋙ forget₂ _ _)` is lax monoidal: the structure maps are obtained
objectwise from the lax monoidal structure on `ModuleCat.restrictScalars`.

If `F : C ⥤ D`, `R : Dᵒᵖ ⥤ CommRingCat`, `S : Cᵒᵖ ⥤ CommRingCat` and
`φ : S ⋙ forget₂ _ _ ⟶ (F.op ⋙ R) ⋙ forget₂ _ _`, we deduce that
`PresheafOfModules.pushforward φ` is lax monoidal, since it is the composition of the
(strong) monoidal functor `PresheafOfModules.pushforward₀OfCommRingCat F R` with
`PresheafOfModules.restrictScalars φ`. Dually, when the pullback functor exists, i.e.
when `PresheafOfModules.pushforward φ` has a left adjoint, `PresheafOfModules.pullback φ`
is oplax monoidal.

## Implementation notes

The presheaf of rings `(F.op ⋙ R) ⋙ forget₂ _ _` appearing in the type of `φ` is only
definitionally equal to the presheaf `F.op ⋙ (R ⋙ forget₂ _ _)` that `pushforward`
expects, so the arguments `F`, `R` and `S` of `pushforward` and `pullback` have to be
provided explicitly. The type of `φ` is chosen so that it is the one obtained by
whiskering a morphism `S ⟶ F.op ⋙ R` of presheaves of commutative rings with
`forget₂ CommRingCat RingCat`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules

section

variable {C : Type u₁} [Category.{v₁} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{u}}
  (α : R ⋙ forget₂ CommRingCat RingCat ⟶ R' ⋙ forget₂ CommRingCat RingCat)

open ModuleCat.MonoidalCategory in
noncomputable instance : (restrictScalars.{u} α).LaxMonoidal where
  ε :=
    { app X := ε (ModuleCat.restrictScalars (α.app X).hom)
      naturality {X Y} f := by
        refine ModuleCat.hom_ext
          (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun r ↦ ?_))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
          ModuleCat.restrictScalars.map_apply, Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
          Functor.comp_map, CommRingCat.forgetToRingCat_map_hom]
        erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
        exact RingHom.congr_fun (congrArg RingCat.Hom.hom (α.naturality f)) r }
  μ M₁ M₂ :=
    { app X := μ (ModuleCat.restrictScalars (α.app X).hom) (M₁.obj X) (M₂.obj X)
      naturality {X Y} f := by
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro m₁ m₂
        simp only [Functor.comp_obj, CommRingCat.forgetToRingCat_obj, Functor.comp_map,
          CommRingCat.forgetToRingCat_map_hom, ModuleCat.hom_comp, LinearMap.coe_comp,
          Function.comp_apply, ModuleCat.restrictScalars.map_apply]
        erw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
        rfl }
  μ_natural_left {M₁ M₂} f M₃ := by
    ext1 X
    exact μ_natural_left (F := ModuleCat.restrictScalars (α.app X).hom) (f.app X) (M₃.obj X)
  μ_natural_right M₁ f := by
    ext1 X
    exact μ_natural_right (F := ModuleCat.restrictScalars (α.app X).hom) (M₁.obj X) (f.app X)
  associativity M₁ M₂ M₃ := by
    ext1 X
    exact associativity (F := ModuleCat.restrictScalars (α.app X).hom)
      (M₁.obj X) (M₂.obj X) (M₃.obj X)
  left_unitality M := by
    ext1 X
    exact left_unitality (F := ModuleCat.restrictScalars (α.app X).hom) (M.obj X)
  right_unitality M := by
    ext1 X
    exact right_unitality (F := ModuleCat.restrictScalars (α.app X).hom) (M.obj X)

@[simp]
lemma restrictScalars_ε_app (X : Cᵒᵖ) :
    (ε (restrictScalars.{u} α)).app X = ε (ModuleCat.restrictScalars (α.app X).hom) :=
  rfl

@[simp]
lemma restrictScalars_μ_app (M₁ M₂ : PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat))
    (X : Cᵒᵖ) :
    (μ (restrictScalars.{u} α) M₁ M₂).app X =
      μ (ModuleCat.restrictScalars (α.app X).hom) (M₁.obj X) (M₂.obj X) :=
  rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)

noncomputable instance :
    (pushforward.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ).LaxMonoidal :=
  inferInstanceAs ((pushforward₀OfCommRingCat F R ⋙ restrictScalars φ).LaxMonoidal)

noncomputable instance
    [(pushforward.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ).IsRightAdjoint] :
    (pullback.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ).OplaxMonoidal :=
  (pullbackPushforwardAdjunction.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ).leftAdjointOplaxMonoidal

end

end PresheafOfModules
