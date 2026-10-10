/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal

/-!
# Oplax monoidal functors on homological complexes and homotopy categories

Let `G : C ⥤ D` be an additive oplax monoidal functor which preserves the coproducts
defining the tensor product of homological complexes of shape `c`. We show that the functor
`G.mapHomologicalComplex c` is oplax monoidal
(`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexOplaxMonoidal`): its comonoidal
structure is `mapHomologicalComplexδNatTrans c G` and its counit
`mapHomologicalComplexη c G : G(𝟙_) ⟶ 𝟙_` is induced by `η G` on the single complex
`𝟙_ = (single C c 0).obj (𝟙_ C)`. The coherence axioms are checked on the summands
`G((K.X p ⊗ L.X q) ⊗ M.X r)` of `G(((K ⊗ L) ⊗ M).X n)`, where they reduce to the axioms
for `G`.
When `δ G` and `η G` are isomorphisms, `G.mapHomologicalComplex c` is monoidal
(`mapHomologicalComplexMonoidal`).

The same holds for the functor `G.mapHomotopyCategory c` induced on homotopy categories
(`mapHomotopyCategoryOplaxMonoidal`, `mapHomotopyCategoryMonoidal`), with comonoidal
structure `mapHomotopyCategoryδNatTrans c G`; the coherence axioms are deduced from those on
homological complexes by applying `HomotopyCategory.quotient`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace HomologicalComplex.Monoidal

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The morphism `(f ▷ L).f n` on the summand `K.X p ⊗ L.X q` is `f.f p ▷ L.X q`. -/
@[reassoc]
lemma ιTensorObj_whiskerRight_f {K K' : HomologicalComplex C c} (f : K ⟶ K')
    (L : HomologicalComplex C c) (p q n : I) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ (f ▷ L).f n = f.f p ▷ L.X q ≫ ιTensorObj K' L p q n h := by
  erw [ι_mapBifunctorMap]
  simp

/-- The morphism `(K ◁ f).f n` on the summand `K.X p ⊗ L.X q` is `K.X p ◁ f.f q`. -/
@[reassoc]
lemma ιTensorObj_whiskerLeft_f (K : HomologicalComplex C c) {L L' : HomologicalComplex C c}
    (f : L ⟶ L') (p q n : I) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ (K ◁ f).f n = K.X p ◁ f.f q ≫ ιTensorObj K L' p q n h := by
  erw [ι_mapBifunctorMap]
  simp

/-- The associator of homological complexes on the summand `(K.X p ⊗ L.X q) ⊗ M.X r`. -/
@[reassoc]
lemma ιTensorObj_associator_hom_f (K L M : HomologicalComplex C c) (p q r s t n : I)
    (hs : p + q = s) (ht : q + r = t) (h : s + r = n) (h' : p + t = n) :
    ιTensorObj K L p q s hs ▷ M.X r ≫ ιTensorObj (K ⊗ L) M s r n h ≫ (α_ K L M).hom.f n =
      (α_ (K.X p) (L.X q) (M.X r)).hom ≫ K.X p ◁ ιTensorObj L M q r t ht ≫
        ιTensorObj K (L ⊗ M) p t n h' := by
  subst hs ht h
  exact (assoc _ _ _).symm.trans (HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso C) K L M (c₁₂ := c) (c₂₃ := c) (c₄ := c) p q r _ rfl)

/-- The degree `n` component of the inverse of the left unitor of homological complexes. -/
lemma leftUnitor_inv_f (K : HomologicalComplex C c) (n : I) :
    (λ_ K).inv.f n = (λ_ (K.X n)).inv ≫ (singleObjXSelf c 0 (𝟙_ C)).inv ▷ K.X n ≫
      ιTensorObj (𝟙_ (HomologicalComplex C c)) K 0 n n (zero_add n) :=
  leftUnitor'_inv K n

/-- The degree `n` component of the inverse of the right unitor of homological complexes. -/
lemma rightUnitor_inv_f (K : HomologicalComplex C c) (n : I) :
    (ρ_ K).inv.f n = (ρ_ (K.X n)).inv ≫ K.X n ◁ (singleObjXSelf c 0 (𝟙_ C)).inv ≫
      ιTensorObj K (𝟙_ (HomologicalComplex C c)) n 0 n (add_zero n) :=
  rightUnitor'_inv K n

end HomologicalComplex.Monoidal

namespace CategoryTheory.Functor.OplaxMonoidal

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
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G]

/-- The counit `G(𝟙_) ⟶ 𝟙_` of the functor induced by `G` on homological complexes: the
unit complex is `(single C c 0).obj (𝟙_ C)`, and this is `(single D c 0).map (η G)` up to
the identification `G((single C c 0).obj X) ≅ (single D c 0).obj (G X)`. -/
noncomputable def mapHomologicalComplexη :
    (G.mapHomologicalComplex c).obj (𝟙_ (HomologicalComplex C c)) ⟶
      𝟙_ (HomologicalComplex D c) :=
  (singleMapHomologicalComplex G c 0).hom.app (𝟙_ C) ≫ (single D c 0).map (η G)

omit [Preadditive D] [MonoidalCategory D] [HasZeroObject D] [(curriedTensor D).Additive]
  [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject I D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [G.Additive] [G.OplaxMonoidal] in
/-- Morphisms out of `G(((K ⊗ L) ⊗ M).X n)` are determined by their restrictions to the
summands `G((K.X p ⊗ L.X q) ⊗ M.X r)`, as `G` preserves the coproducts involved. -/
lemma map_tensorObj₁₂_hom_ext {K L M : HomologicalComplex C c} {n : I} {B : D}
    {f g : G.obj (((K ⊗ L) ⊗ M).X n) ⟶ B}
    (hfg : ∀ (p q r s : I) (hs : p + q = s) (h : s + r = n),
      G.map (ιTensorObj K L p q s hs ▷ M.X r) ≫ G.map (ιTensorObj (K ⊗ L) M s r n h) ≫ f =
        G.map (ιTensorObj K L p q s hs ▷ M.X r) ≫
          G.map (ιTensorObj (K ⊗ L) M s r n h) ≫ g) :
    f = g := by
  refine mapBifunctor.hom_ext_of_map G (fun s r h ↦ ?_)
  have : PreservesColimit (Discrete.functor (GradedObject.mapObjFun
    (((GradedObject.mapBifunctor (curriedTensor C) I I).obj K.X).obj L.X)
      (ComplexShape.π c c c) s)) ((curriedTensor C).flip.obj (M.X r) ⋙ G) := inferInstance
  have : PreservesColimit (Discrete.functor (fun (x : ComplexShape.π c c c ⁻¹' {s}) ↦
    K.X x.1.1 ⊗ L.X x.1.2)) ((curriedTensor C).flip.obj (M.X r) ⋙ G) := this
  have hc : IsColimit (Cofan.mk ((K ⊗ L).X s)
      (fun (x : ComplexShape.π c c c ⁻¹' {s}) ↦ ιTensorObj K L x.1.1 x.1.2 s x.2)) :=
    GradedObject.isColimitCofanMapObj _ _ s
  exact Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
    ((curriedTensor C).flip.obj (M.X r) ⋙ G) _ _ hc) _ _
    (fun x ↦ by simpa [assoc] using hfg x.1.1 x.1.2 r s x.2 h)

omit [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G] in
/-- The degree `0` component of `mapHomologicalComplexη c G` is `η G`. -/
@[reassoc]
lemma map_singleObjXSelf_inv_mapHomologicalComplexη_f :
    G.map (singleObjXSelf c 0 (𝟙_ C)).inv ≫ (mapHomologicalComplexη c G).f 0 =
      η G ≫ (singleObjXSelf c 0 (𝟙_ D)).inv := by
  dsimp only [mapHomologicalComplexη, HomologicalComplex.comp_f]
  rw [singleMapHomologicalComplex_hom_app_self, single_map_f_self]
  erw [assoc, Iso.inv_hom_id_assoc, ← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, id_comp]

/-- Auxiliary morphism for the associativity of `mapHomologicalComplexδNatTrans`:
the composition `G((X ⊗ Y) ⊗ Z) ⟶ G(X ⊗ Y) ⊗ G Z ⟶ (G X ⊗ G Y) ⊗ G Z` on the
summands. -/
noncomputable def δ₁₂X (K L M : HomologicalComplex C c) (p q r : I) :
    G.obj ((K.X p ⊗ L.X q) ⊗ M.X r) ⟶ (((G.mapHomologicalComplex c).obj K).X p ⊗
      ((G.mapHomologicalComplex c).obj L).X q) ⊗ ((G.mapHomologicalComplex c).obj M).X r :=
  δ G _ _ ≫ δ G (K.X p) (L.X q) ▷ G.obj (M.X r)

/-- Auxiliary computation for the associativity of the comparison of `G.mapHomologicalComplex`
on the summands `G((K.X p ⊗ L.X q) ⊗ M.X r)`. -/
lemma map_whiskerRight_comparisonApp_comparison_f (K L M : HomologicalComplex C c)
    (p q r s : I) (hs : p + q = s) {Z : D}
    (φ : (((G.mapHomologicalComplex c).obj K ⊗ (G.mapHomologicalComplex c).obj L).X s ⊗
      ((G.mapHomologicalComplex c).obj M).X r) ⟶ Z) :
    G.map (ιTensorObj K L p q s hs ▷ M.X r) ≫
      mapBifunctorComparisonApp (δNatTrans G) (K ⊗ L) M s r ≫
        (mapBifunctorComparison (δNatTrans G) c K L).f s ▷
          ((G.mapHomologicalComplex c).obj M).X r ≫ φ =
      δ₁₂X c G K L M p q r ≫ ιTensorObj ((G.mapHomologicalComplex c).obj K)
        ((G.mapHomologicalComplex c).obj L) p q s hs ▷ ((G.mapHomologicalComplex c).obj M).X r ≫
          φ := by
  have e₁ := δ_natural_left G (ιTensorObj K L p q s hs) (M.X r)
  have e₂ := map_ιMapBifunctor_mapBifunctorComparisonX (δNatTrans G) c K L p q s hs
  erw [← reassoc_of% e₁, ← comp_whiskerRight_assoc, mapBifunctorComparison_f, e₂,
    comp_whiskerRight, δ₁₂X, assoc, assoc]
  rfl

/-- Auxiliary morphism for the associativity of `mapHomologicalComplexδNatTrans`:
the composition `G(X ⊗ (Y ⊗ Z)) ⟶ G X ⊗ G(Y ⊗ Z) ⟶ G X ⊗ (G Y ⊗ G Z)` on the
summands. -/
noncomputable def δ₂₃X (K L M : HomologicalComplex C c) (p q r : I) :
    G.obj (K.X p ⊗ (L.X q ⊗ M.X r)) ⟶ ((G.mapHomologicalComplex c).obj K).X p ⊗
      (((G.mapHomologicalComplex c).obj L).X q ⊗ ((G.mapHomologicalComplex c).obj M).X r) :=
  δ G _ _ ≫ G.obj (K.X p) ◁ δ G (L.X q) (M.X r)

/-- Auxiliary computation for the associativity of the comparison of `G.mapHomologicalComplex`
on the summands `G(K.X p ⊗ (L.X q ⊗ M.X r))`. -/
lemma map_whiskerLeft_comparisonApp_comparison_f (K L M : HomologicalComplex C c)
    (p q r t : I) (ht : q + r = t) {Z : D}
    (φ : ((G.mapHomologicalComplex c).obj K).X p ⊗
      (((G.mapHomologicalComplex c).obj L ⊗ (G.mapHomologicalComplex c).obj M).X t) ⟶ Z) :
    G.map (K.X p ◁ ιTensorObj L M q r t ht) ≫
      mapBifunctorComparisonApp (δNatTrans G) K (L ⊗ M) p t ≫
        ((G.mapHomologicalComplex c).obj K).X p ◁
          (mapBifunctorComparison (δNatTrans G) c L M).f t ≫ φ =
      δ₂₃X c G K L M p q r ≫ ((G.mapHomologicalComplex c).obj K).X p ◁
        ιTensorObj ((G.mapHomologicalComplex c).obj L) ((G.mapHomologicalComplex c).obj M)
          q r t ht ≫ φ := by
  have e₁ := δ_natural_right G (K.X p) (ιTensorObj L M q r t ht)
  have e₂ := map_ιMapBifunctor_mapBifunctorComparisonX (δNatTrans G) c L M q r t ht
  erw [← reassoc_of% e₁, ← MonoidalCategory.whiskerLeft_comp_assoc, mapBifunctorComparison_f,
    e₂,     MonoidalCategory.whiskerLeft_comp, δ₂₃X, assoc, assoc]
  rfl

omit [AddMonoid I] [c.TensorSigns] [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  [DecidableEq I] [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject I D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G] in
/-- The associativity axiom of `G` in terms of `δ₁₂X` and `δ₂₃X`. -/
lemma map_associator_hom_δ₂₃X (K L M : HomologicalComplex C c) (p q r : I) :
    G.map (α_ (K.X p) (L.X q) (M.X r)).hom ≫ δ₂₃X c G K L M p q r =
      δ₁₂X c G K L M p q r ≫ (α_ _ _ _).hom := by
  dsimp only [δ₁₂X, δ₂₃X]
  exact ((assoc _ _ _).trans (oplax_associativity G (K.X p) (L.X q) (M.X r))).symm

open HomologicalComplex.Monoidal in
/-- The associativity axiom for `G.mapHomologicalComplex c`, on the summand
`G((K.X p ⊗ L.X q) ⊗ M.X r)` of `G(((K ⊗ L) ⊗ M).X n)`. -/
lemma map_ιTensorObj_ιTensorObj_oplax_associativity (K L M : HomologicalComplex C c)
    (p q r s n : I) (hs : p + q = s) (h : s + r = n) :
    G.map (ιTensorObj K L p q s hs ▷ M.X r) ≫ G.map (ιTensorObj (K ⊗ L) M s r n h) ≫
      mapBifunctorComparisonX (δNatTrans G) c (K ⊗ L) M n ≫
        (mapBifunctorComparison (δNatTrans G) c K L ▷ (G.mapHomologicalComplex c).obj M).f n ≫
          (α_ ((G.mapHomologicalComplex c).obj K) ((G.mapHomologicalComplex c).obj L)
            ((G.mapHomologicalComplex c).obj M)).hom.f n =
    G.map (ιTensorObj K L p q s hs ▷ M.X r) ≫ G.map (ιTensorObj (K ⊗ L) M s r n h) ≫
      G.map ((α_ K L M).hom.f n) ≫ mapBifunctorComparisonX (δNatTrans G) c K (L ⊗ M) n ≫
        ((G.mapHomologicalComplex c).obj K ◁
          mapBifunctorComparison (δNatTrans G) c L M).f n := by
  have hn : p + (q + r) = n := by rw [← h, ← hs, add_assoc]
  rw [map_ιMapBifunctor_mapBifunctorComparisonX_assoc, ιTensorObj_whiskerRight_f_assoc,
    map_whiskerRight_comparisonApp_comparison_f]
  erw [ιTensorObj_associator_hom_f _ _ _ p q r s (q + r) n hs rfl h hn]
  rw [← G.map_comp_assoc, ← G.map_comp_assoc, assoc,
    ιTensorObj_associator_hom_f _ _ _ p q r s (q + r) n hs rfl h hn,
    G.map_comp_assoc, G.map_comp_assoc, map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  have e : ιMapBifunctor ((G.mapHomologicalComplex c).obj K)
      ((G.mapHomologicalComplex c).obj (L ⊗ M)) (curriedTensor D) c p (q + r) n
        hn ≫
      ((G.mapHomologicalComplex c).obj K ◁ mapBifunctorComparison (δNatTrans G) c L M).f n =
      ((G.mapHomologicalComplex c).obj K).X p ◁ (mapBifunctorComparison (δNatTrans G) c L M).f
        (q + r) ≫ ιTensorObj _ _ p (q + r) n hn :=
    ιTensorObj_whiskerLeft_f _ _ _ _ _ _
  rw [e, map_whiskerLeft_comparisonApp_comparison_f, reassoc_of% map_associator_hom_δ₂₃X]
  rfl

open HomologicalComplex.Monoidal in
/-- The left unitality axiom for `G.mapHomologicalComplex c`, in degree `n`. -/
lemma oplax_left_unitality_f (K : HomologicalComplex C c) (n : I) :
    (λ_ ((G.mapHomologicalComplex c).obj K)).inv.f n =
      G.map ((λ_ K).inv.f n) ≫ mapBifunctorComparisonX (δNatTrans G) c (𝟙_ _) K n ≫
        (mapHomologicalComplexη c G ▷ (G.mapHomologicalComplex c).obj K).f n := by
  have e : ιMapBifunctor ((G.mapHomologicalComplex c).obj (𝟙_ (HomologicalComplex C c)))
      ((G.mapHomologicalComplex c).obj K) (curriedTensor D) c 0 n n (zero_add n) ≫
      (mapHomologicalComplexη c G ▷ (G.mapHomologicalComplex c).obj K).f n =
      (mapHomologicalComplexη c G).f 0 ▷ ((G.mapHomologicalComplex c).obj K).X n ≫
        ιTensorObj _ _ 0 n n (zero_add n) :=
    ιTensorObj_whiskerRight_f _ _ _ _ _ _
  have e₁ := δ_natural_left G (singleObjXSelf c 0 (𝟙_ C)).inv (K.X n)
  rw [leftUnitor_inv_f, leftUnitor_inv_f, G.map_comp_assoc, G.map_comp_assoc,
    map_ιMapBifunctor_mapBifunctorComparisonX_assoc, e]
  erw [← reassoc_of% e₁, ← comp_whiskerRight_assoc,
    map_singleObjXSelf_inv_mapHomologicalComplexη_f, comp_whiskerRight_assoc,
    ← OplaxMonoidal.left_unitality_assoc]
  rfl

open HomologicalComplex.Monoidal in
/-- The right unitality axiom for `G.mapHomologicalComplex c`, in degree `n`. -/
lemma oplax_right_unitality_f (K : HomologicalComplex C c) (n : I) :
    (ρ_ ((G.mapHomologicalComplex c).obj K)).inv.f n =
      G.map ((ρ_ K).inv.f n) ≫ mapBifunctorComparisonX (δNatTrans G) c K (𝟙_ _) n ≫
        ((G.mapHomologicalComplex c).obj K ◁ mapHomologicalComplexη c G).f n := by
  have e : ιMapBifunctor ((G.mapHomologicalComplex c).obj K)
      ((G.mapHomologicalComplex c).obj (𝟙_ (HomologicalComplex C c))) (curriedTensor D) c n 0 n
        (add_zero n) ≫
      ((G.mapHomologicalComplex c).obj K ◁ mapHomologicalComplexη c G).f n =
      ((G.mapHomologicalComplex c).obj K).X n ◁ (mapHomologicalComplexη c G).f 0 ≫
        ιTensorObj _ _ n 0 n (add_zero n) :=
    ιTensorObj_whiskerLeft_f _ _ _ _ _ _
  have e₁ := δ_natural_right G (K.X n) (singleObjXSelf c 0 (𝟙_ C)).inv
  rw [rightUnitor_inv_f, rightUnitor_inv_f, G.map_comp_assoc, G.map_comp_assoc,
    map_ιMapBifunctor_mapBifunctorComparisonX_assoc, e]
  erw [← reassoc_of% e₁, ← MonoidalCategory.whiskerLeft_comp_assoc,
    map_singleObjXSelf_inv_mapHomologicalComplexη_f, MonoidalCategory.whiskerLeft_comp_assoc,
    ← OplaxMonoidal.right_unitality_assoc]
  rfl

variable
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), X₁.HasTensor₄ObjExt X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), X₁.HasTensor₄ObjExt X₂ X₃ X₄]

/-- An additive oplax monoidal functor `G : C ⥤ D` preserving the relevant coproducts induces
an oplax monoidal functor on homological complexes. -/
noncomputable instance mapHomologicalComplexOplaxMonoidal :
    (G.mapHomologicalComplex c).OplaxMonoidal where
  η := mapHomologicalComplexη c G
  δ K L := mapBifunctorComparison (δNatTrans G) c K L
  δ_natural_left f L := (congr_app ((mapHomologicalComplexδNatTrans c G).naturality f) L).symm
  δ_natural_right K f := (((mapHomologicalComplexδNatTrans c G).app K).naturality f).symm
  oplax_associativity K L M := by
    ext n
    exact map_tensorObj₁₂_hom_ext c G (fun p q r s hs h ↦
      map_ιTensorObj_ιTensorObj_oplax_associativity c G K L M p q r s n hs h)
  oplax_left_unitality K := by
    ext n
    exact oplax_left_unitality_f c G K n
  oplax_right_unitality K := by
    ext n
    exact oplax_right_unitality_f c G K n

@[simp]
lemma mapHomologicalComplex_η : η (G.mapHomologicalComplex c) = mapHomologicalComplexη c G := rfl

@[simp]
lemma mapHomologicalComplex_δ (K L : HomologicalComplex C c) :
    δ (G.mapHomologicalComplex c) K L = ((mapHomologicalComplexδNatTrans c G).app K).app L :=
  rfl

section Monoidal

variable [∀ X Y : C, IsIso (δ G X Y)] [IsIso (η G)]

instance : IsIso (mapHomologicalComplexη c G) := by
  rw [mapHomologicalComplexη]
  infer_instance

instance : IsIso (η (G.mapHomologicalComplex c)) :=
  inferInstanceAs (IsIso (mapHomologicalComplexη c G))

instance (K L : HomologicalComplex C c) : IsIso (δ (G.mapHomologicalComplex c) K L) :=
  inferInstanceAs (IsIso (mapBifunctorComparison (δNatTrans G) c K L))

/-- If the structure morphisms of `G` are isomorphisms, the functor induced on homological
complexes is monoidal. -/
noncomputable instance mapHomologicalComplexMonoidal : (G.mapHomologicalComplex c).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

lemma mapHomologicalComplex_μ (K L : HomologicalComplex C c) :
    LaxMonoidal.μ (G.mapHomologicalComplex c) K L =
      CategoryTheory.inv (((mapHomologicalComplexδNatTrans c G).app K).app L) :=
  rfl

end Monoidal

section HomotopyCategory

open HomotopyCategory.MonoidalCategory

/-- The counit `G(𝟙_) ⟶ 𝟙_` of the functor induced by `G` on homotopy categories. -/
noncomputable def mapHomotopyCategoryη :
    (G.mapHomotopyCategory c).obj (𝟙_ (HomotopyCategory C c)) ⟶ 𝟙_ (HomotopyCategory D c) :=
  (HomotopyCategory.quotient D c).map (mapHomologicalComplexη c G)

/-- The associator of the homotopy category on objects of the form `quotient.obj K`. -/
lemma _root_.HomotopyCategory.associator_hom_quotient_obj (K L M : HomologicalComplex C c) :
    (α_ ((HomotopyCategory.quotient C c).obj K) ((HomotopyCategory.quotient C c).obj L)
      ((HomotopyCategory.quotient C c).obj M)).hom =
        (HomotopyCategory.quotient C c).map (α_ K L M).hom :=
  associator_hom_app_app_app K L M

/-- The inverse left unitor of the homotopy category on objects `quotient.obj K`. -/
lemma _root_.HomotopyCategory.leftUnitor_inv_quotient_obj (K : HomologicalComplex C c) :
    (λ_ ((HomotopyCategory.quotient C c).obj K)).inv =
      (HomotopyCategory.quotient C c).map (λ_ K).inv := by
  refine Iso.inv_ext ((congrArg (· ≫ (HomotopyCategory.quotient C c).map (λ_ K).inv)
    (HomotopyCategory.MonoidalCategory.leftUnitor_hom_app K)).trans ?_)
  erw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
  rfl

/-- The inverse right unitor of the homotopy category on objects `quotient.obj K`. -/
lemma _root_.HomotopyCategory.rightUnitor_inv_quotient_obj (K : HomologicalComplex C c) :
    (ρ_ ((HomotopyCategory.quotient C c).obj K)).inv =
      (HomotopyCategory.quotient C c).map (ρ_ K).inv := by
  refine Iso.inv_ext ((congrArg (· ≫ (HomotopyCategory.quotient C c).map (ρ_ K).inv)
    (HomotopyCategory.MonoidalCategory.rightUnitor_hom_app K)).trans ?_)
  erw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
  rfl

/-- An additive oplax monoidal functor `G : C ⥤ D` preserving the relevant coproducts induces
an oplax monoidal functor on homotopy categories. -/
noncomputable instance mapHomotopyCategoryOplaxMonoidal :
    (G.mapHomotopyCategory c).OplaxMonoidal where
  η := mapHomotopyCategoryη c G
  δ K L := ((mapHomotopyCategoryδNatTrans c G).app K).app L
  δ_natural_left f L := (congr_app ((mapHomotopyCategoryδNatTrans c G).naturality f) L).symm
  δ_natural_right K f := (((mapHomotopyCategoryδNatTrans c G).app K).naturality f).symm
  oplax_associativity K L M := by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨L, rfl⟩ := L.quotient_obj_surjective
    obtain ⟨M, rfl⟩ := M.quotient_obj_surjective
    have h := (HomotopyCategory.quotient D c).congr_map
      (oplax_associativity (G.mapHomologicalComplex c) K L M)
    simp only [Functor.map_comp] at h
    rw [← HomotopyCategory.associator_hom_quotient_obj, ← Functor.mapHomotopyCategory_map,
      ← HomotopyCategory.associator_hom_quotient_obj] at h
    exact h
  oplax_left_unitality K := by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    have h := (HomotopyCategory.quotient D c).congr_map
      (oplax_left_unitality (G.mapHomologicalComplex c) K)
    simp only [Functor.map_comp] at h
    rw [← HomotopyCategory.leftUnitor_inv_quotient_obj, ← Functor.mapHomotopyCategory_map,
      ← HomotopyCategory.leftUnitor_inv_quotient_obj] at h
    exact h
  oplax_right_unitality K := by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    have h := (HomotopyCategory.quotient D c).congr_map
      (oplax_right_unitality (G.mapHomologicalComplex c) K)
    simp only [Functor.map_comp] at h
    rw [← HomotopyCategory.rightUnitor_inv_quotient_obj, ← Functor.mapHomotopyCategory_map,
      ← HomotopyCategory.rightUnitor_inv_quotient_obj] at h
    exact h

@[simp]
lemma mapHomotopyCategory_η : η (G.mapHomotopyCategory c) = mapHomotopyCategoryη c G := rfl

@[simp]
lemma mapHomotopyCategory_δ (K L : HomotopyCategory C c) :
    δ (G.mapHomotopyCategory c) K L = ((mapHomotopyCategoryδNatTrans c G).app K).app L :=
  rfl

section Monoidal

variable [∀ X Y : C, IsIso (δ G X Y)] [IsIso (η G)]

instance : IsIso (η (G.mapHomotopyCategory c)) :=
  inferInstanceAs (IsIso ((HomotopyCategory.quotient D c).map (mapHomologicalComplexη c G)))

instance (K L : HomotopyCategory C c) : IsIso (δ (G.mapHomotopyCategory c) K L) :=
  inferInstanceAs (IsIso (((mapHomotopyCategoryδNatTrans c G).app K).app L))

/-- If the structure morphisms of `G` are isomorphisms, the functor induced on homotopy
categories is monoidal. -/
noncomputable instance mapHomotopyCategoryMonoidal : (G.mapHomotopyCategory c).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

lemma mapHomotopyCategory_μ (K L : HomotopyCategory C c) :
    LaxMonoidal.μ (G.mapHomotopyCategory c) K L =
      CategoryTheory.inv (((mapHomotopyCategoryδNatTrans c G).app K).app L) :=
  rfl

end Monoidal

end HomotopyCategory

end CategoryTheory.Functor.OplaxMonoidal
