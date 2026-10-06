/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.SpectralObject

/-!
# Spectral objects in abelian categories from triangulated spectral objects

Let `X : Triangulated.SpectralObject C ι` be a spectral object in a pretriangulated
category `C`, and `F : C ⥤ A` a homological functor to an abelian category `A`
equipped with a shift sequence `F.ShiftSequence ℤ`. In this file, we construct
`X.mapHomologicalFunctor F : Abelian.SpectralObject A ι`: its functors are
`H n := X.ω₁ ⋙ F.shift n`, and the connecting homomorphisms are given by the
connecting homomorphisms `F.homologySequenceδ` of the long exact sequences obtained
by applying `F` to the functorial distinguished triangles `X.ω₂`.

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Triangulated.SpectralObject

variable {C ι A : Type*} [Category* C] [Category* ι] [Category* A] [Abelian A]
  [HasZeroObject C] [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] (X : SpectralObject C ι) (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

/-- The spectral object in an abelian category `A` that is obtained by applying
a homological functor `F : C ⥤ A` (with a shift sequence) to a spectral object
in a pretriangulated category `C`. -/
noncomputable def mapHomologicalFunctor : Abelian.SpectralObject A ι where
  H n := X.ω₁ ⋙ F.shift n
  δ' n₀ n₁ h :=
    { app D := F.homologySequenceδ (X.ω₂.obj D) n₀ n₁ h
      naturality _ _ φ := F.homologySequenceδ_naturality _ _ (X.ω₂.map φ) n₀ n₁ h }
  exact₁' n₀ n₁ h D :=
    (F.homologySequence_exact₁ _ (X.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows
  exact₂' n D :=
    (F.homologySequence_exact₂ _ (X.ω₂_obj_distinguished D) n).exact_toComposableArrows
  exact₃' n₀ n₁ h D :=
    (F.homologySequence_exact₃ _ (X.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows

@[simp]
lemma mapHomologicalFunctor_H (n : ℤ) :
    (X.mapHomologicalFunctor F).H n = X.ω₁ ⋙ F.shift n := rfl

/-- The connecting homomorphisms of `X.mapHomologicalFunctor F` are the connecting
homomorphisms of the homology sequences of the distinguished triangles `X.triangle f g`. -/
lemma mapHomologicalFunctor_δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    (X.mapHomologicalFunctor F).δ f g n₀ n₁ h =
      F.homologySequenceδ (X.triangle f g) n₀ n₁ h := rfl

end Triangulated.SpectralObject

namespace Functor

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  [HasZeroObject C] [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The functor from spectral objects in a pretriangulated category `C` to spectral
objects in an abelian category `A` that is induced by a homological functor `F : C ⥤ A`
equipped with a shift sequence. -/
noncomputable def mapHomologicalSpectralObject (F : C ⥤ A) [F.IsHomological]
    [F.ShiftSequence ℤ] (ι : Type*) [Category* ι] :
    Triangulated.SpectralObject C ι ⥤ Abelian.SpectralObject A ι where
  obj X := X.mapHomologicalFunctor F
  map α :=
    { hom n := Functor.whiskerRight α.hom (F.shift n)
      comm n₀ n₁ h i j k f g := by
        simp only [Triangulated.SpectralObject.mapHomologicalFunctor_δ, homologySequenceδ,
          Triangulated.SpectralObject.triangle_mor₃, whiskerRight_app, ← shiftMap_comp,
          ← shiftMap_comp', Triangulated.SpectralObject.Hom.comm] }

@[simp]
lemma mapHomologicalSpectralObject_map_hom (F : C ⥤ A) [F.IsHomological]
    [F.ShiftSequence ℤ] (ι : Type*) [Category* ι] {X Y : Triangulated.SpectralObject C ι}
    (α : X ⟶ Y) (n : ℤ) :
    ((F.mapHomologicalSpectralObject ι).map α).hom n =
      Functor.whiskerRight α.hom (F.shift n) := rfl

end Functor

end CategoryTheory
