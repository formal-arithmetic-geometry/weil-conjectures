/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor

/-!
# Complements on the tensor product of cochain complexes

For cochain complexes indexed by `ℤ`, we describe the differential of the tensor product
`P ⊗ K` and the morphism `P ◁ f` on the summands `P.X p ⊗ K.X q`.

If `G : C ⥤ D` is an additive oplax monoidal functor which preserves the coproducts
defining the tensor product of complexes, the comonoidal structure of `G` induces
a natural transformation `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` of bifunctors on homological complexes
(`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans`), which is an
isomorphism when every `δ G X Y` is an isomorphism. These comparisons are compatible with
composition of functors
(`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_comp`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (P K : CochainComplex C ℤ)

lemma tensorObj_d_eq (r r' : ℤ) :
    (P ⊗ K).d r r' = (HomologicalComplex.tensorObj P K).d r r' := rfl

variable {K} in
lemma whiskerLeft_f_eq {K' : CochainComplex C ℤ} (f : K ⟶ K') (r : ℤ) :
    (P ◁ f).f r = (HomologicalComplex.tensorHom (𝟙 P) f).f r := rfl

/-- The differential of `P ⊗ K` on the summand `P.X p ⊗ K.X q` of `(P ⊗ K).X r`:
```
P.X p ⊗ K.X q ───────── ιTensorObj ─────────▶ (P ⊗ K).X r
      │                                              │
      │ (d_P ▷ K.X q, (-1)ᵖ • P.X p ◁ d_K)           │ (P ⊗ K).d r r'
      ▼                                              ▼
P.X (p + 1) ⊗ K.X q ⊞ P.X p ⊗ K.X (q + 1) ─ ιTensorObj ─▶ (P ⊗ K).X r'
```
-/
@[reassoc]
lemma ιTensorObj_d (p q r r' : ℤ) (h : p + q = r) (h' : r + 1 = r') :
    HomologicalComplex.ιTensorObj P K p q r h ≫ (P ⊗ K).d r r' =
      P.d p (p + 1) ▷ K.X q ≫ HomologicalComplex.ιTensorObj P K (p + 1) q r' (by lia) +
        p.negOnePow • (P.X p ◁ K.d q (q + 1) ≫
          HomologicalComplex.ιTensorObj P K p (q + 1) r' (by lia)) := by
  rw [tensorObj_d_eq, HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _
      (show p + 1 + q = r' by lia),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _
      (show p + (q + 1) = r' by lia)]
  simp

variable {K} in
/-- The morphism `P ◁ f` on the summand `P.X p ⊗ K.X q` of `(P ⊗ K).X r`:
```
P.X p ⊗ K.X q  ── ιTensorObj ──▶ (P ⊗ K).X r
      │                               │
      │ P.X p ◁ f.f q                 │ (P ◁ f).f r
      ▼                               ▼
P.X p ⊗ K'.X q ── ιTensorObj ──▶ (P ⊗ K').X r
```
-/
@[reassoc]
lemma ιTensorObj_whiskerLeft_f {K' : CochainComplex C ℤ} (f : K ⟶ K') (p q r : ℤ)
    (h : p + q = r) :
    HomologicalComplex.ιTensorObj P K p q r h ≫ (P ◁ f).f r =
      P.X p ◁ f.f q ≫ HomologicalComplex.ιTensorObj P K' p q r h := by
  rw [whiskerLeft_f_eq]
  simp

end CochainComplex

namespace CategoryTheory.Functor.OplaxMonoidal

open HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns] [DecidableEq I]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject I D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G]

/-- The comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` for homological complexes `K` and `L`, induced
by the comonoidal structure `δ` of an additive oplax monoidal functor `G` which preserves the
coproducts `(K ⊗ L).X n = ∐_{p + q = n} K.X p ⊗ L.X q`. It is
`HomologicalComplex.mapBifunctorComparisonNatTrans` applied to `δNatTrans G`: on the summand
`G(K.X p ⊗ L.X q)` it is given by
```
G(K.X p ⊗ L.X q) ──── G(ιTensorObj) ────▶ G((K ⊗ L).X n)
       │                                       │
       │ δ G (K.X p) (L.X q)                   │ comparison
       ▼                                       ▼
G(K.X p) ⊗ G(L.X q) ─── ιTensorObj ───▶ (G(K) ⊗ G(L)).X n
```
-/
noncomputable def mapHomologicalComplexδNatTrans :
    (Functor.postcompose₂.obj (G.mapHomologicalComplex c)).obj
        (curriedTensor (HomologicalComplex C c)) ⟶
      (((whiskeringLeft₂ _).obj (G.mapHomologicalComplex c)).obj
        (G.mapHomologicalComplex c)).obj (curriedTensor (HomologicalComplex D c)) :=
  mapBifunctorComparisonNatTrans (δNatTrans G) c

@[simp]
lemma mapHomologicalComplexδNatTrans_app_app (K L : HomologicalComplex C c) :
    ((mapHomologicalComplexδNatTrans c G).app K).app L =
      mapBifunctorComparison (δNatTrans G) c K L := rfl

variable [∀ X Y : C, IsIso (δ G X Y)]

instance : IsIso (mapHomologicalComplexδNatTrans c G) :=
  inferInstanceAs (IsIso (mapBifunctorComparisonNatTrans (δNatTrans G) c))

end CategoryTheory.Functor.OplaxMonoidal

namespace CategoryTheory.Functor.OplaxMonoidal

open HomologicalComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  [(curriedTensor E).Additive] [∀ (X₁ : E), ((curriedTensor E).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns] [DecidableEq I]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject I D), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject I E), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {G₁ : C ⥤ D} {G₂ : D ⥤ E} {G₁₂ : C ⥤ E} [G₁.Additive] [G₂.Additive] [G₁₂.Additive]
  [G₁.OplaxMonoidal] [G₂.OplaxMonoidal] [G₁₂.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G₁]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G₂]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G₁₂]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `u : G₁₂ ⟶ G₁ ⋙ G₂` be compatible with the comparisons `δ` of the oplax monoidal
functors `G₁`, `G₂` and `G₁₂`. Then the induced morphism of functors on homological complexes is
compatible with the comparisons `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` of
`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans`:
```
  G₁₂(K ⊗ L) ──────────u──────────▶ G₂(G₁(K ⊗ L))
       │                                  │ G₂(δ)
       │ δ                                ▼
       │                           G₂(G₁K ⊗ G₁L)
       │                                  │ δ
       ▼                                  ▼
  G₁₂K ⊗ G₁₂L ───────u ⊗ u───────▶ G₂G₁K ⊗ G₂G₁L
```
-/
lemma mapHomologicalComplexδNatTrans_comp (u : G₁₂ ⟶ G₁ ⋙ G₂)
    (hu : ∀ X Y : C, u.app (X ⊗ Y) ≫ G₂.map (δ G₁ X Y) ≫ δ G₂ _ _ =
      δ G₁₂ X Y ≫ (u.app X ⊗ₘ u.app Y))
    (K L : HomologicalComplex C c) :
    (NatTrans.mapHomologicalComplex u c).app (K ⊗ L) ≫
        (G₂.mapHomologicalComplex c).map (((mapHomologicalComplexδNatTrans c G₁).app K).app L) ≫
        ((mapHomologicalComplexδNatTrans c G₂).app _).app _ =
      ((mapHomologicalComplexδNatTrans c G₁₂).app K).app L ≫
        ((NatTrans.mapHomologicalComplex u c).app K ⊗ₘ
          (NatTrans.mapHomologicalComplex u c).app L) := by
  ext j
  refine mapBifunctor.hom_ext_of_map G₁₂ (fun i₁ i₂ h ↦ ?_)
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    mapHomologicalComplexδNatTrans_app_app, Functor.mapHomologicalComplex_map_f,
    mapBifunctorComparison_f, map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [u.naturality_assoc, Functor.comp_map, ← G₂.map_comp_assoc,
    map_ιMapBifunctor_mapBifunctorComparisonX, G₂.map_comp, assoc,
    map_ιMapBifunctor_mapBifunctorComparisonX, ι_mapBifunctorMap]
  erw [reassoc_of% (hu (K.X i₁) (L.X i₂)), tensorHom_def, assoc]
  rfl

end CategoryTheory.Functor.OplaxMonoidal
