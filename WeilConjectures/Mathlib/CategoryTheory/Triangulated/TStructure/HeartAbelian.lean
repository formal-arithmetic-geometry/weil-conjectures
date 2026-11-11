/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# The heart of a t-structure is abelian

Let `t` be a t-structure on a triangulated category `C`. The full subcategory `t.heart` of the
objects which are both `≤ 0` and `≥ 0` is an abelian category
([BBD, Théorème 1.3.6][bbd-1982]). We deduce this from the criterion
`CategoryTheory.Triangulated.AbelianSubcategory.abelian`: there are no negative extensions
between objects of the heart, and the cone `X₃` of a morphism of the heart, which lies in
`[-1, 0]`, sits in a truncation triangle `(τ_{≤ -1} X₃) ⟶ X₃ ⟶ τ_{≥ 0} X₃ ⟶` whose outer terms
are, up to shift, in the heart.

## Main declarations

- `CategoryTheory.Triangulated.TStructure.heartAbelian`: the abelian structure on the heart.
- `CategoryTheory.Triangulated.TStructure.exists_abelian_heart`: the heart of a t-structure is
  abelian, with its given preadditive structure.
-/

@[expose] public section

namespace CategoryTheory.Triangulated.TStructure

open Limits Pretriangulated ZeroObject

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- An object of the heart of `t` lies in degrees `≤ 0`. -/
lemma isLE_of_heart {X : C} (hX : t.heart X) : t.IsLE X 0 :=
  ((t.mem_heart_iff X).1 hX).1

/-- An object of the heart of `t` lies in degrees `≥ 0`. -/
lemma isGE_of_heart {X : C} (hX : t.heart X) : t.IsGE X 0 :=
  ((t.mem_heart_iff X).1 hX).2

/-- The heart of a t-structure is closed under extensions. -/
lemma heart_obj₂ (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : t.heart T.obj₁)
    (h₃ : t.heart T.obj₃) : t.heart T.obj₂ :=
  (t.mem_heart_iff _).2
    ⟨t.isLE₂ T hT 0 (t.isLE_of_heart h₁) (t.isLE_of_heart h₃),
      t.isGE₂ T hT 0 (t.isGE_of_heart h₁) (t.isGE_of_heart h₃)⟩

instance : t.heart.ContainsZero where
  exists_zero := ⟨0, isZero_zero C, (t.mem_heart_iff _).2 ⟨inferInstance, inferInstance⟩⟩

instance : t.heart.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine t.heart.prop_of_iso ?_ (t.heart_obj₂ _
      (binaryProductTriangle_distinguished _ _)
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

instance : t.heart.IsClosedUnderFiniteProducts := .mk'

/-- There are no negative extensions between objects of the heart. -/
lemma heart_hom_shift_eq_zero {X Y : t.heart.FullSubcategory} {n : ℤ}
    (f : t.heart.ι.obj X ⟶ (t.heart.ι.obj Y)⟦n⟧) (hn : n < 0) : f = 0 := by
  have : t.IsLE (t.heart.ι.obj X) 0 := t.isLE_of_heart X.property
  have : t.IsGE (t.heart.ι.obj Y) 0 := t.isGE_of_heart Y.property
  have := t.isGE_shift (t.heart.ι.obj Y) 0 n (-n) (by lia)
  exact t.zero f 0 (-n) (by lia)

/-- Every morphism of the heart is admissible: the cone `X₃` of a morphism of the heart lies in
degrees `[-1, 0]`, and its truncation triangle `τ_{≤ -1} X₃ ⟶ X₃ ⟶ τ_{≥ 0} X₃ ⟶` has its outer
terms in the heart, up to the shift by `1`. -/
lemma admissibleMorphism_heart_eq_top [IsTriangulated C] :
    AbelianSubcategory.admissibleMorphism t.heart.ι = ⊤ := by
  ext X₁ X₂ f₁
  simp only [MorphismProperty.top_apply, iff_true]
  intro X₃ f₂ f₃ hT
  have : t.IsLE (t.heart.ι.obj X₁) 0 := t.isLE_of_heart X₁.property
  have : t.IsGE (t.heart.ι.obj X₁) 0 := t.isGE_of_heart X₁.property
  have : t.IsLE (t.heart.ι.obj X₂) 0 := t.isLE_of_heart X₂.property
  have : t.IsGE (t.heart.ι.obj X₂) 0 := t.isGE_of_heart X₂.property
  have := t.isLE_shift (t.heart.ι.obj X₁) 0 1 (-1) (by lia)
  have h₁ : t.IsLE ((t.heart.ι.obj X₁)⟦(1 : ℤ)⟧) 0 := t.isLE_of_le _ (-1) 0
  have h₁' : t.IsGE ((t.heart.ι.obj X₁)⟦(1 : ℤ)⟧) (-1) := t.isGE_shift _ 0 1 (-1) (by lia)
  have hT' := rot_of_distTriang _ hT
  have hle : t.IsLE X₃ 0 :=
    t.isLE₂ _ hT' 0 (show t.IsLE (t.heart.ι.obj X₂) 0 from inferInstance) h₁
  have hge : t.IsGE X₃ (-1) := t.isGE₂ _ hT' (-1) (t.isGE_of_ge (t.heart.ι.obj X₂) (-1) 0) h₁'
  obtain ⟨A, B, hA, hB, a, b, c, hT₃⟩ := t.exists_triangle X₃ (-1) 0 (by lia)
  have := (t.le_iff_isLE _ _).1 hA
  have := (t.ge_iff_isGE _ _).1 hB
  -- `B` is an extension of `X₃` and `A⟦1⟧`, so it lies in `≤ 0`
  have hBle : t.IsLE B 0 := by
    have := t.isLE_shift A (-1) 1 (-2) (by lia)
    have := t.isLE_of_le (A⟦(1 : ℤ)⟧) (-2) 0
    exact t.isLE₂ _ (rot_of_distTriang _ hT₃) 0 hle
      (show t.IsLE (A⟦(1 : ℤ)⟧) 0 from inferInstance)
  -- `A` is an extension of `B⟦-1⟧` and `X₃`, so it lies in `≥ -1`
  have hAge : t.IsGE A (-1) := by
    have := t.isGE_shift B 0 (-1) 1 (by lia)
    have := t.isGE_of_ge (B⟦(-1 : ℤ)⟧) (-1) 1
    exact t.isGE₂ _ (inv_rot_of_distTriang _ hT₃) (-1)
      (show t.IsGE (B⟦(-1 : ℤ)⟧) (-1) from inferInstance) hge
  have hK : t.heart (A⟦(-1 : ℤ)⟧) := (t.mem_heart_iff _).2
    ⟨t.isLE_shift A (-1) (-1) 0 (by lia), t.isGE_shift A (-1) (-1) 0 (by lia)⟩
  let K : t.heart.FullSubcategory := ⟨A⟦(-1 : ℤ)⟧, hK⟩
  let Q : t.heart.FullSubcategory := ⟨B, (t.mem_heart_iff _).2 ⟨hBle, inferInstance⟩⟩
  let e : (t.heart.ι.obj K)⟦(1 : ℤ)⟧ ≅ A := (shiftFunctorCompIsoId C (-1 : ℤ) 1 (by lia)).app A
  refine ⟨K, Q, e.hom ≫ a, b, c ≫ e.inv⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT₃ _ ?_⟩
  exact Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (by simp [← Functor.map_comp])

/-- **The heart of a t-structure is abelian** ([BBD, Théorème 1.3.6][bbd-1982]), with the
preadditive structure of the full subcategory. -/
@[instance_reducible]
noncomputable def heartAbelian [IsTriangulated C] : Abelian t.heart.FullSubcategory :=
  AbelianSubcategory.abelian t.heart.ι (fun _ _ _ f hn ↦ t.heart_hom_shift_eq_zero f hn)
    t.admissibleMorphism_heart_eq_top

/-- **The heart of a t-structure is abelian** ([BBD, Théorème 1.3.6][bbd-1982]): there is an
abelian structure on `t.heart.FullSubcategory` whose preadditive structure is that of the full
subcategory. -/
theorem exists_abelian_heart [IsTriangulated C] :
    ∃ h : Abelian t.heart.FullSubcategory,
      h.toPreadditive = (inferInstance : Preadditive t.heart.FullSubcategory) :=
  ⟨t.heartAbelian, rfl⟩

end CategoryTheory.Triangulated.TStructure
