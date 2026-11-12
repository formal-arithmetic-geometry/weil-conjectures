/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# t-exactness of equivalences

Let `t₁` and `t₂` be t-structures on pretriangulated categories `C` and `D`. A fully faithful
essentially surjective functor `F : C ⥤ D` which reflects the classes `≤ n` preserves the classes
`≥ n`, as these are the right orthogonals of the classes `≤ n - 1`.

## Main statements

- `CategoryTheory.Triangulated.TStructure.isGE_obj_of_reflects_isLE`.
- `CategoryTheory.Functor.tExact_of_preserves_of_reflects_isLE`: a triangulated equivalence which
  preserves and reflects the classes `≤ n` is t-exact.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] (t₁ : Triangulated.TStructure C)
  (t₂ : Triangulated.TStructure D)

namespace Triangulated.TStructure

/-- A fully faithful essentially surjective functor `F` which reflects the classes `≤ n`
carries objects `≥ n` to objects `≥ n`: a morphism `M ⟶ F X` with `M ≅ F Y` and `M ≤ n - 1` is
the image of a morphism `Y ⟶ X` from `Y ≤ n - 1`, which vanishes. -/
lemma isGE_obj_of_reflects_isLE (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj]
    (hF : ∀ (Y : C) (n : ℤ), t₂.IsLE (F.obj Y) n → t₁.IsLE Y n) (X : C) (n : ℤ)
    [t₁.IsGE X n] : t₂.IsGE (F.obj X) n := by
  rw [t₂.isGE_iff_orthogonal (n - 1) n (by lia)]
  intro M f _
  let e := F.objObjPreimageIso M
  have : t₁.IsLE (F.objPreimage M) (n - 1) := hF _ _ (t₂.isLE_of_iso e.symm _)
  obtain ⟨g, hg⟩ := F.map_surjective (e.hom ≫ f)
  rw [← cancel_epi e.hom, comp_zero, ← hg, t₁.zero g (n - 1) n (by lia), F.map_zero]

end Triangulated.TStructure

/-- A triangulated equivalence which preserves and reflects the classes `≤ n` of two
t-structures is t-exact: it preserves the classes `≥ n` by
`CategoryTheory.Triangulated.TStructure.isGE_obj_of_reflects_isLE`. -/
lemma Functor.tExact_of_preserves_of_reflects_isLE (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] [F.Full] [F.Faithful] [F.EssSurj]
    (hF : ∀ (Y : C) (n : ℤ), t₂.IsLE (F.obj Y) n ↔ t₁.IsLE Y n) : F.TExact t₁ t₂ :=
  { rightTExact := .mk F t₁ t₂ fun Y _ ↦ (hF Y 0).2 inferInstance
    leftTExact := .mk F t₁ t₂ fun X _ ↦
      t₁.isGE_obj_of_reflects_isLE t₂ F (fun Y n ↦ (hF Y n).1) X 0 }

end CategoryTheory
