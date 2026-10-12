/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TruncationTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# The truncation triangles in the bounded below derived category

The canonical truncations `τ_{≤ n}` and the functors `H^q(-)[-q]` of
`WeilConjectures.CategoryTheory.DerivedCategory.TruncationTriangle` preserve bounded below
objects, so they restrict to the bounded below derived category `D⁺(C)`
(`DerivedCategory.Plus.truncLE`, `DerivedCategory.Plus.homologySingleFunctor`), and so do the
truncation triangles

`τ_{≤ q₀} X ⟶ τ_{≤ q} X ⟶ H^q(X)[-q] ⟶ (τ_{≤ q₀} X)⟦1⟧`   (`q₀ + 1 = q`),

which are distinguished in `D⁺(C)` (`DerivedCategory.Plus.truncLETriangle_distinguished`). This is
the last assertion of blueprint `lem-weil-pbc-truncation-triangle`: for a bounded below object
the truncation triangle lies in `D⁺`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

variable (C) in
/-- The canonical truncation functor `τ_{≤ n}` on the bounded below derived category. -/
noncomputable def truncLE (n : ℤ) : Plus C ⥤ Plus C :=
  (DerivedCategory.TStructure.t (C := C)).plus.lift (ι ⋙ DerivedCategory.truncLE C n)
    (fun X ↦ by
      obtain ⟨a, ha⟩ := X.2
      have : (ι.obj X).IsGE a := ha
      exact ⟨a, DerivedCategory.isGE_truncLE_obj (ι.obj X) a n⟩)

variable (C) in
/-- The functor `X ↦ H^q(X)[-q]` on the bounded below derived category. -/
noncomputable def homologySingleFunctor (q : ℤ) : Plus C ⥤ Plus C :=
  (DerivedCategory.TStructure.t (C := C)).plus.lift
    (ι ⋙ DerivedCategory.homologySingleFunctor C q)
    (fun X ↦ ⟨q, inferInstanceAs (((DerivedCategory.singleFunctor C q).obj _).IsGE q)⟩)

@[simp]
lemma ι_obj_truncLE_obj (n : ℤ) (X : Plus C) :
    ι.obj ((truncLE C n).obj X) = (DerivedCategory.truncLE C n).obj (ι.obj X) := rfl

@[simp]
lemma ι_map_truncLE_map (n : ℤ) {X Y : Plus C} (f : X ⟶ Y) :
    ι.map ((truncLE C n).map f) = (DerivedCategory.truncLE C n).map (ι.map f) := rfl

@[simp]
lemma ι_obj_homologySingleFunctor_obj (q : ℤ) (X : Plus C) :
    ι.obj ((homologySingleFunctor C q).obj X) =
      (DerivedCategory.homologySingleFunctor C q).obj (ι.obj X) := rfl

@[simp]
lemma ι_map_homologySingleFunctor_map (q : ℤ) {X Y : Plus C} (f : X ⟶ Y) :
    ι.map ((homologySingleFunctor C q).map f) =
      (DerivedCategory.homologySingleFunctor C q).map (ι.map f) := rfl

variable (C) in
/-- The isomorphism between `DerivedCategory.Plus.homologySingleFunctor C q` and the composite
of the homology functor in degree `q` and the single functor in degree `q`. -/
noncomputable def homologySingleFunctorIso (q : ℤ) :
    homologySingleFunctor C q ≅ homologyFunctor C q ⋙ singleFunctor C q :=
  Iso.refl _

variable (C) in
/-- The inclusion `τ_{≤ a} ⟶ τ_{≤ b}` on `D⁺(C)`, for `a ≤ b`. -/
noncomputable def truncLEMapOfLE (a b : ℤ) (h : a ≤ b) : truncLE C a ⟶ truncLE C b where
  app X := ObjectProperty.homMk ((DerivedCategory.truncLEMapOfLE C a b h).app (ι.obj X))
  naturality _ _ f := by
    ext
    exact (DerivedCategory.truncLEMapOfLE C a b h).naturality (ι.map f)

@[simp]
lemma ι_map_truncLEMapOfLE_app (a b : ℤ) (h : a ≤ b) (X : Plus C) :
    ι.map ((truncLEMapOfLE C a b h).app X) =
      (DerivedCategory.truncLEMapOfLE C a b h).app (ι.obj X) := rfl

variable (C) in
/-- The morphism `τ_{≤ n} ⟶ 𝟭` on `D⁺(C)`. -/
noncomputable def truncLEι (n : ℤ) : truncLE C n ⟶ 𝟭 _ where
  app X := ObjectProperty.homMk ((DerivedCategory.truncLEι C n).app (ι.obj X))
  naturality _ _ f := by
    ext
    exact (DerivedCategory.truncLEι C n).naturality (ι.map f)

@[simp]
lemma ι_map_truncLEι_app (n : ℤ) (X : Plus C) :
    ι.map ((truncLEι C n).app X) = (DerivedCategory.truncLEι C n).app (ι.obj X) := rfl

variable (C) in
/-- The projection `τ_{≤ q} ⟶ H^q(-)[-q]` on `D⁺(C)`. -/
noncomputable def truncLEToHomologySingle (q : ℤ) : truncLE C q ⟶ homologySingleFunctor C q where
  app X := ObjectProperty.homMk ((DerivedCategory.truncLEToHomologySingle C q).app (ι.obj X))
  naturality _ _ f := by
    ext
    exact (DerivedCategory.truncLEToHomologySingle C q).naturality (ι.map f)

@[simp]
lemma ι_map_truncLEToHomologySingle_app (q : ℤ) (X : Plus C) :
    ι.map ((truncLEToHomologySingle C q).app X) =
      (DerivedCategory.truncLEToHomologySingle C q).app (ι.obj X) := rfl

section Triangle

variable (q₀ q : ℤ) (hq : q₀ + 1 = q)

/-- The connecting morphism `H^q(-)[-q] ⟶ τ_{≤ q₀}(-)⟦1⟧` of the truncation triangles in
`D⁺(C)`. -/
noncomputable def truncLEδ :
    homologySingleFunctor C q ⟶ truncLE C q₀ ⋙ shiftFunctor (Plus C) (1 : ℤ) where
  app X := ObjectProperty.homMk ((DerivedCategory.truncLEδ q₀ q hq).app (ι.obj X) ≫
    (ι.commShiftIso (1 : ℤ)).inv.app ((truncLE C q₀).obj X))
  naturality _ _ f := by
    ext
    have h₁ := (DerivedCategory.truncLEδ q₀ q hq).naturality (ι.map f)
    have h₂ := (ι.commShiftIso (1 : ℤ)).inv.naturality ((truncLE C q₀).map f)
    dsimp at h₁ h₂ ⊢
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
    rw [reassoc_of% h₁]
    exact congrArg (fun φ ↦ _ ≫ φ) h₂.symm

lemma ι_map_truncLEδ_app (X : Plus C) :
    ι.map ((truncLEδ q₀ q hq).app X) ≫ (ι.commShiftIso (1 : ℤ)).hom.app ((truncLE C q₀).obj X) =
      (DerivedCategory.truncLEδ q₀ q hq).app (ι.obj X) := by
  change (_ ≫ _) ≫ _ = _
  rw [assoc, Iso.inv_hom_id_app, comp_id]

/-- The truncation triangles `τ_{≤ q₀} X ⟶ τ_{≤ q} X ⟶ H^q(X)[-q] ⟶ (τ_{≤ q₀} X)⟦1⟧` in the
bounded below derived category, as a functor `D⁺(C) ⥤ Triangle D⁺(C)`. -/
noncomputable def truncLETriangle : Plus C ⥤ Triangle (Plus C) :=
  Triangle.functorMk (truncLEMapOfLE C q₀ q (by lia)) (truncLEToHomologySingle C q)
    (truncLEδ q₀ q hq)

/-- The truncation triangles in `D⁺(C)` are the truncation triangles in `D(C)`. -/
noncomputable def mapTriangleιTruncLETriangleIso (X : Plus C) :
    ι.mapTriangle.obj ((truncLETriangle q₀ q hq).obj X) ≅
      (DerivedCategory.truncLETriangle q₀ q hq).obj (ι.obj X) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [truncLETriangle,
    DerivedCategory.truncLETriangle]) (by simp [truncLETriangle,
    DerivedCategory.truncLETriangle]) (by
      dsimp [truncLETriangle, DerivedCategory.truncLETriangle]
      rw [Functor.map_id, comp_id, id_comp, ι_map_truncLEδ_app])

/-- This is blueprint `lem-weil-pbc-truncation-triangle` in `D⁺(C)`: the truncation triangles of
a bounded below object are distinguished triangles of the bounded below derived category. -/
lemma truncLETriangle_distinguished (X : Plus C) :
    (truncLETriangle q₀ q hq).obj X ∈ distTriang (Plus C) :=
  isomorphic_distinguished _ (DerivedCategory.truncLETriangle_distinguished q₀ q hq (ι.obj X))
    _ (mapTriangleιTruncLETriangleIso q₀ q hq X)

end Triangle

end DerivedCategory.Plus
