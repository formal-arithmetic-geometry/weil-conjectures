/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.SpectralObject
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic

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

namespace Triangulated.SpectralObject

variable {C ι : Type*} [Category* C] [Category* ι] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Constructor for isomorphisms of spectral objects in a pretriangulated category: an
isomorphism `X.ω₁ ≅ Y.ω₁` which commutes with the connecting homomorphisms. -/
@[simps]
def isoMk {X Y : SpectralObject C ι} (e : X.ω₁ ≅ Y.ω₁)
    (comm : ∀ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k),
      X.δ f g ≫ (e.hom.app (mk₁ f))⟦(1 : ℤ)⟧' = e.hom.app (mk₁ g) ≫ Y.δ f g) :
    X ≅ Y where
  hom := { hom := e.hom, comm := comm }
  inv :=
    { hom := e.inv
      comm f g := by
        rw [← cancel_epi (e.hom.app (mk₁ g)), ← reassoc_of% (comm f g), ← Functor.map_comp,
          Iso.hom_inv_id_app, Functor.map_id, Category.comp_id, Iso.hom_inv_id_app_assoc] }
  hom_inv_id := SpectralObject.hom_ext e.hom_inv_id
  inv_hom_id := SpectralObject.hom_ext e.inv_hom_id

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

section NatTrans

variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A natural transformation `τ : F₁ ⟶ F₂` between triangulated functors which commutes with the
shifts induces a natural transformation between the functors induced on spectral objects. -/
@[simps]
def _root_.CategoryTheory.NatTrans.mapTriangulatedSpectralObject {F₁ F₂ : C ⥤ D}
    [F₁.CommShift ℤ] [F₁.IsTriangulated] [F₂.CommShift ℤ] [F₂.IsTriangulated] (τ : F₁ ⟶ F₂)
    [NatTrans.CommShift τ ℤ] (ι : Type*) [Category* ι] :
    F₁.mapTriangulatedSpectralObject ι ⟶ F₂.mapTriangulatedSpectralObject ι where
  app X :=
    { hom := Functor.whiskerLeft X.ω₁ τ
      comm f g := by
        change (F₁.map (X.δ f g) ≫ (F₁.commShiftIso (1 : ℤ)).hom.app _) ≫ _ =
          _ ≫ F₂.map (X.δ f g) ≫ (F₂.commShiftIso (1 : ℤ)).hom.app _
        simp only [Category.assoc, NatTrans.shift_app_comm, NatTrans.naturality_assoc,
          Functor.whiskerLeft_app] }
  naturality X Y α := by
    ext1
    ext D
    simp only [Triangulated.SpectralObject.comp_hom, NatTrans.comp_app]
    change F₁.map (α.hom.app D) ≫ τ.app _ = τ.app _ ≫ F₂.map (α.hom.app D)
    exact τ.naturality (α.hom.app D)

variable {E : Type*} [Category* E] [HasZeroObject E] [Preadditive E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

end NatTrans

section Exact

variable {D A' : Type*} [Category* D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [Category* A'] [Abelian A']
  (H : C ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
  (H' : D ⥤ A') [H'.IsHomological] [H'.ShiftSequence ℤ]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  (γ : A ⥤ A') [γ.Additive] [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
  (e : ∀ n : ℤ, H.shift n ⋙ γ ≅ F ⋙ H'.shift n)
  (he : ∀ (a a' : ℤ) (h : 1 + a = a') (X : C),
    γ.map ((H.shiftIso 1 a a' h).hom.app X) ≫ (e a').hom.app X =
      (e a).hom.app (X⟦(1 : ℤ)⟧) ≫ (H'.shift a).map ((F.commShiftIso (1 : ℤ)).hom.app X) ≫
        (H'.shiftIso 1 a a' h).hom.app (F.obj X))

end Exact

end Functor

end CategoryTheory
