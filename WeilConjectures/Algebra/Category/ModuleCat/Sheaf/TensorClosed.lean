/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
-- Additive tensor functors supply the four MonoidalPreadditive fields below.
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree

/-!
# Tensor closed structure on sheaves of modules

## References

* Stacks Project, Modules on Sites, Section 03EK and Lemma 03EO
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Compatibility abbreviation for the existing additive symmetric monoidal closed structure
on sheaves of modules, with internal Hom `SheafOfModules.homObj`.
The family of tensor-Hom equivalences
commutes with precomposition in both tensor factors and postcomposition in the target.
This packages `monoidalClosed`, `tensorHomEquiv`, their naturality lemmas and the
additivity instances of `tensorLeft` and `tensorRight`; it adds no new tensor or Hom data. -/
abbrev tensorClosed (R : Sheaf J CommRingCat.{u}) :
    letI := monoidalCategory R
    letI := symmetricCategory R
    Nonempty (MonoidalPreadditive (SheafOfModules.{u} (𝓡 R))) ∧
      Nonempty (MonoidalClosed (SheafOfModules.{u} (𝓡 R))) ∧
        ∃ e : ∀ (F G H : SheafOfModules.{u} (𝓡 R)),
            (F ⊗ G ⟶ H) ≃ (G ⟶ homObj F H),
          ∀ (F F' G G' H H' : SheafOfModules.{u} (𝓡 R))
            (f : F' ⟶ F) (g : G' ⟶ G) (h : H ⟶ H') (t : F ⊗ G ⟶ H),
            e F' G' H' ((f ⊗ₘ g) ≫ t ≫ h) =
              g ≫ e F G H t ≫ homObjMap f h := by
  let := monoidalCategory R
  let := symmetricCategory R
  refine ⟨⟨?_⟩, ⟨monoidalClosed⟩, tensorHomEquiv, ?_⟩
  · -- MonoidalFree supplies additivity of both tensor functors from the adjunction.
    exact
      { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
        add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  · intro F F' G G' H H' f g h t
    -- Naturality in the two tensor factors precedes naturality in the target.
    rw [tensorHom_def, Category.assoc]
    calc
      tensorHomEquiv F' G' H' (f ▷ G' ≫ F ◁ g ≫ t ≫ h) =
          tensorHomEquiv F G' H' (F ◁ g ≫ t ≫ h) ≫ homObjMap f (𝟙 H') :=
        tensorHomEquiv_whiskerRight_comp f _
      _ = (g ≫ tensorHomEquiv F G H' (t ≫ h)) ≫ homObjMap f (𝟙 H') := by
        rw [tensorHomEquiv_whiskerLeft_comp]
      _ = g ≫ tensorHomEquiv F G H t ≫ homObjMap f h := by
        rw [tensorHomEquiv_comp_homObjMap]
        simp only [Category.assoc, homObjMap_comp_homObjMap, Category.comp_id]

end SheafOfModules
