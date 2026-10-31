/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData

/-! # Evaluation-transpose compatibility of realization reindexing

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
private theorem uncurry_formula {A : Type*} [Category* A]
    {H : Aᵒᵖ × A ⥤ A} (S : CoefficientClosedStructure H)
    {L M N : A} (f : L ⟶ H.obj (Opposite.op M, N)) :
    (S.transpose L M N).symm f =
      S.tensor.map (Prod.mkHom f (𝟙 M)) ≫ S.evaluation M N := by
  change (@MonoidalCategory.tensorRight A _ S.monoidal M).map f ≫
    S.evaluation M N = _
  let := S.monoidal
  simp [CoefficientClosedStructure.tensor]

private theorem evaluation_both {A : Type*} [Category* A]
    {H : Aᵒᵖ × A ⥤ A} (S : CoefficientClosedStructure H)
    (M M' N N' : A) (a : M' ⟶ M) (b : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op b)) (𝟙 M')) ≫
      S.evaluation M' N' =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (Opposite.op M, N))) a) ≫
      S.evaluation M N ≫ b := by
  have hs : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 N))) (𝟙 M')) ≫
      S.evaluation M' N =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (Opposite.op M, N))) a) ≫
        S.evaluation M N := by
    simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor] using
      S.evaluation_naturality M M' N a
  have ht : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (Opposite.op M')) b))
      (𝟙 M')) ≫ S.evaluation M' N' = S.evaluation M' N ≫ b := by
    simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
      Prod.sectR] using (S.adjunction M').counit.naturality b
  have hh : Prod.mkHom a.op b =
      Prod.mkHom a.op (𝟙 N) ≫ Prod.mkHom (𝟙 (Opposite.op M')) b := by simp
  rw [hh, H.map_comp]
  have hh' : Prod.mkHom
      (H.map (Prod.mkHom a.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (Opposite.op M')) b))
        (𝟙 M') =
      Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 N))) (𝟙 M') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (Opposite.op M')) b)) (𝟙 M') := by simp
  rw [hh', S.tensor.map_comp, Category.assoc, ht, ← Category.assoc, hs, Category.assoc]

private theorem uncurry_transport {A : Type*} [Category* A]
    {H : Aᵒᵖ × A ⥤ A} (S : CoefficientClosedStructure H)
    {L L' M M' N N' : A} (a : L' ⟶ L) (b : M' ⟶ M) (c : N ⟶ N')
    (f : L ⟶ H.obj (Opposite.op M, N)) :
    (S.transpose L' M' N').symm (a ≫ f ≫ H.map (Prod.mkHom b.op c)) =
      S.tensor.map (Prod.mkHom a b) ≫ (S.transpose L M N).symm f ≫ c := by
  rw [uncurry_formula, uncurry_formula]
  have ht : Prod.mkHom (a ≫ f ≫ H.map (Prod.mkHom b.op c)) (𝟙 M') =
      Prod.mkHom (a ≫ f) (𝟙 M') ≫
        Prod.mkHom (H.map (Prod.mkHom b.op c)) (𝟙 M') := by simp
  rw [ht, S.tensor.map_comp, Category.assoc, evaluation_both]
  simp only [← Functor.map_comp_assoc, prod_comp,
    Category.comp_id, Category.id_comp, Category.assoc]

-- This calculation only uses the tensor square at (Hom(M,N),M), its evaluation
-- square, and the defining evaluation identities of the two Hom comparisons.
private theorem hom_square
    {A B : Type*} [Category* A] [Category* B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (G : A ⥤ B) (μ : SA.tensor ⋙ G ≅ G.prod G ⋙ SB.tensor)
    {J M N V : A} {J' M' N' V' : B}
    (iJ : J' ≅ G.obj J) (iM : M' ≅ G.obj M) (iN : N' ≅ G.obj N)
    (iV : V' ≅ G.obj V)
    (t : SA.tensor.obj (J, M) ⟶ V) (t' : SB.tensor.obj (J', M') ⟶ V')
    (e : V ⟶ N) (e' : V' ⟶ N')
    (h_tensor : G.map t ≫ iV.inv =
      μ.hom.app (J, M) ≫ SB.tensor.map (Prod.mkHom iJ.inv iM.inv) ≫ t')
    (h_eval : iV.hom ≫ G.map e = e' ≫ iN.hom)
    (h : J ⟶ HA.obj (Opposite.op M, N))
    (h' : J' ⟶ HB.obj (Opposite.op M', N'))
    (he : (SA.transpose J M N).symm h = t ≫ e)
    (he' : (SB.transpose J' M' N').symm h' = t' ≫ e') :
    iJ.hom ≫ G.map h ≫
      SB.transpose _ _ _ (μ.inv.app (HA.obj (Opposite.op M, N), M) ≫
        G.map (SA.evaluation M N)) ≫
      HB.map (Prod.mkHom iM.hom.op iN.inv) = h' := by
  have h_tensor' : SB.tensor.map (Prod.mkHom iJ.hom iM.hom) ≫
      μ.inv.app (J, M) ≫ G.map t = t' ≫ iV.hom := by
    have ht := congrArg (fun z ↦ SB.tensor.map (Prod.mkHom iJ.hom iM.hom) ≫
      μ.inv.app (J, M) ≫ z ≫ iV.hom) h_tensor
    have hij : SB.tensor.map (Prod.mkHom iJ.hom iM.hom) ≫
        SB.tensor.map (Prod.mkHom iJ.inv iM.inv) = 𝟙 _ := by
      rw [← SB.tensor.map_comp]
      convert SB.tensor.map_id (J', M') using 1
      simp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_app_assoc] at ht
    rw [reassoc_of% hij] at ht
    exact ht
  apply (SB.transpose J' M' N').symm.injective
  rw [← Category.assoc iJ.hom (G.map h), uncurry_transport,
    Equiv.symm_apply_apply, he']
  have hn := μ.inv.naturality (Prod.mkHom h (𝟙 M))
  change SB.tensor.map (Prod.mkHom (G.map h) (G.map (𝟙 M))) ≫
      μ.inv.app (HA.obj (Opposite.op M, N), M) =
    μ.inv.app (J, M) ≫ G.map (SA.tensor.map (Prod.mkHom h (𝟙 M))) at hn
  rw [G.map_id] at hn
  have hm : Prod.mkHom (iJ.hom ≫ G.map h) iM.hom =
      Prod.mkHom iJ.hom iM.hom ≫ Prod.mkHom (G.map h) (𝟙 (G.obj M)) := by simp
  rw [hm, SB.tensor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [← G.map_comp, ← Category.assoc]
  rw [← uncurry_formula, he]
  rw [G.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h_tensor', reassoc_of% h_eval]
  simp

variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

set_option maxHeartbeats 600000 in
-- The native coefficient and permitted-pair types require extra definitional equality checks.
/-- A tensor-compatible realization comparison preserves the permitted internal Hom map.
Source: Stacks 0GMX; Bhatt--Scholze, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-reindexing-hom).

Proof: Uncurry the asserted equation using the target tensor-Hom adjunction. Naturality
of this adjunction in its parameter and both Hom variables rewrites the left side as
pulled-back realized evaluation, followed by the comparison at the second input.
Here pullHom is by definition the transpose of pulled-back evaluation, so its counit
identity supplies this rewrite. Apply tensor compatibility and naturality of comparison
to the source evaluation arrow. The evaluation equation for the permitted-pair pullback
Hom comparison identifies the result with the uncurrying of the right side. The
realization HomLaws evaluation identities give the same realized evaluation on both
sides. Injectivity of uncurrying proves equality. All Hom objects used are the recorded
permitted pairs; no perfection assertion on their first input is needed. -/
theorem normalized_reindexing_hom
    (C : FamilyCore l D)
    (h_tensor_compatibility : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
          (M N : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) U.base.left),
        letI := (C.data T).units
        letI := (C.data U).units
        (derivedPull l T.base.left g.hom (C.ring T U g)).map ((C.data U).tensor.tensor.hom.app (M,
          N)) ≫
          (C.comparison T U g).inv.app ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj
            (M, N)) ≫
          (ordinary l T.base.left (C.data T).realization).map
            (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom M N).hom =
        (C.pullTensor T U g).tensor.hom.app
            ((ordinary l U.base.left (C.data U).realization).obj M,
             (ordinary l U.base.left (C.data U).realization).obj N) ≫
          (C.data T).tensor.closed.tensor.map (Prod.mkHom
            ((C.comparison T U g).inv.app M) ((C.comparison T U g).inv.app N)) ≫
          (C.data T).tensor.tensor.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj
            M,
            (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N)) :
    ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (P : (commonStageHomPairs l (PadicAlgCl l) U.base.left).FullSubcategory),
    letI := (C.data T).units
    letI := (C.data U).units
    (C.comparison T U g).hom.app
        ((commonStageDerivedInternalHom l (PadicAlgCl l) U.base.left).obj P) ≫
      (derivedPull l T.base.left g.hom (C.ring T U g)).map
        (homComparison l U.base.left (C.data U).realization (C.data U).tensor P) ≫
      pullHom l T.base.left g.hom (C.pullTensor T U g)
        ((ordinary l U.base.left (C.data U).realization).obj P.obj.1.unop)
        ((ordinary l U.base.left (C.data U).realization).obj P.obj.2) ≫
      (ambientHom l T.base.left (C.data T).realization).map
        (Prod.mkHom ((C.comparison T U g).hom.app P.obj.1.unop).op
          ((C.comparison T U g).inv.app P.obj.2)) =
    (ordinary l T.base.left (C.data T).realization).map
        (podCommonHomComparison l (PadicAlgCl l) g.hom P) ≫
      homComparison l T.base.left (C.data T).realization (C.data T).tensor
        ((podPairPullback (commonStageDerivedPullback l (PadicAlgCl l) g.hom)
      (commonStageHomPairs l (PadicAlgCl l) U.base.left)
      (commonStageHomPairs l (PadicAlgCl l) T.base.left)
      (podCommonPairs_pullback l (PadicAlgCl l) g.hom)).obj P) := by
  intro T U g P
  let := (C.data T).units
  let := (C.data U).units
  let F := commonStageDerivedPullback l (PadicAlgCl l) g.hom
  let R := ordinary l T.base.left (C.data T).realization
  let S := ordinary l U.base.left (C.data U).realization
  let G := derivedPull l T.base.left g.hom (C.ring T U g)
  let A := (C.data U).tensor.closed
  let B := (C.data T).tensor.closed
  let H := (commonStageDerivedInternalHom l (PadicAlgCl l) U.base.left).obj P
  let M := P.obj.1.unop
  let N := P.obj.2
  let Q := (podPairPullback F
    (commonStageHomPairs l (PadicAlgCl l) U.base.left)
    (commonStageHomPairs l (PadicAlgCl l) T.base.left)
    (podCommonPairs_pullback l (PadicAlgCl l) g.hom)).obj P
  let κ := podCommonHomComparison l (PadicAlgCl l) g.hom P
  let ν := canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom H M
  let e := (podCommonClosed l (PadicAlgCl l) U.base.left).evaluation P
  let t := (C.data U).tensor.tensor.hom.app (H, M)
  let t' := (C.data T).tensor.tensor.hom.app (F.obj H, F.obj M) ≫ R.map ν.inv
  have ht : G.map t ≫ (C.comparison T U g).inv.app
      ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj (H, M)) =
      (C.pullTensor T U g).tensor.hom.app (S.obj H, S.obj M) ≫
        B.tensor.map (Prod.mkHom ((C.comparison T U g).inv.app H)
          ((C.comparison T U g).inv.app M)) ≫ t' := by
    have hh := congrArg (fun f ↦ f ≫ R.map ν.inv) (h_tensor_compatibility T U g H M)
    have hν : R.map ν.hom ≫ R.map ν.inv = 𝟙 _ := by
      rw [← R.map_comp, Iso.hom_inv_id, R.map_id]
    change (G.map t ≫ (C.comparison T U g).inv.app _ ≫ R.map ν.hom) ≫
      R.map ν.inv = _ at hh
    simp only [Category.assoc] at hh
    rw [hν] at hh
    erw [Category.comp_id] at hh
    simpa only [t', Category.assoc] using hh
  have he : (A.transpose _ _ _).symm
      (homComparison l U.base.left (C.data U).realization (C.data U).tensor P) =
      t ≫ S.map e := by
    rw [uncurry_formula]
    exact (C.data U).hom.evaluation P
  have he' : (B.transpose _ _ _).symm
      (R.map κ ≫ homComparison l T.base.left (C.data T).realization (C.data T).tensor Q) =
      t' ≫ R.map (F.map e) := by
    change (B.transpose (R.obj (F.obj H)) (R.obj (F.obj M)) (R.obj (F.obj N))).symm
      (R.map κ ≫ homComparison l T.base.left (C.data T).realization
        (C.data T).tensor Q) = _
    rw [uncurry_formula]
    have hm : Prod.mkHom
        (R.map κ ≫ homComparison l T.base.left (C.data T).realization (C.data T).tensor Q)
          (𝟙 (R.obj (F.obj M))) =
        Prod.mkHom (R.map κ) (𝟙 (R.obj (F.obj M))) ≫
          Prod.mkHom (homComparison l T.base.left (C.data T).realization
            (C.data T).tensor Q) (𝟙 (R.obj (F.obj M))) := by simp
    rw [hm, B.tensor.map_comp, Category.assoc]
    have heQ := (C.data T).hom.evaluation Q
    change B.tensor.map (Prod.mkHom
      (homComparison l T.base.left (C.data T).realization (C.data T).tensor Q)
        (𝟙 (R.obj (F.obj M)))) ≫ B.evaluation (R.obj (F.obj M)) (R.obj (F.obj N)) =
      (C.data T).tensor.tensor.hom.app
        ((commonStageDerivedInternalHom l (PadicAlgCl l) T.base.left).obj Q, F.obj M) ≫
      R.map ((podCommonClosed l (PadicAlgCl l) T.base.left).evaluation Q) at heQ
    rw [heQ]
    have hn := (C.data T).tensor.tensor.hom.naturality (Prod.mkHom κ (𝟙 (F.obj M)))
    change B.tensor.map (Prod.mkHom (R.map κ) (R.map (𝟙 (F.obj M)))) ≫
        (C.data T).tensor.tensor.hom.app
          ((commonStageDerivedInternalHom l (PadicAlgCl l) T.base.left).obj Q, F.obj M) =
      (C.data T).tensor.tensor.hom.app (F.obj H, F.obj M) ≫
        R.map ((commonStageDerivedTensor l (PadicAlgCl l) T.base.left).map
          (Prod.mkHom κ (𝟙 (F.obj M)))) at hn
    rw [R.map_id] at hn
    rw [← Category.assoc, hn, Category.assoc, ← R.map_comp]
    have hc := (podCommonHomComparison_laws l (PadicAlgCl l) g.hom).evaluation P
    change ν.hom ≫
      (commonStageDerivedTensor l (PadicAlgCl l) T.base.left).map
        (Prod.mkHom κ (𝟙 (F.obj M))) ≫
      (podCommonClosed l (PadicAlgCl l) T.base.left).evaluation Q = F.map e at hc
    have hc'' : (commonStageDerivedTensor l (PadicAlgCl l) T.base.left).map
          (Prod.mkHom κ (𝟙 (F.obj M))) ≫
        (podCommonClosed l (PadicAlgCl l) T.base.left).evaluation Q =
        ν.inv ≫ F.map e := by
      rw [← hc, Iso.inv_hom_id_assoc]
    rw [hc'', R.map_comp]
    exact (Category.assoc _ _ _).symm
  exact hom_square A B G (C.pullTensor T U g).tensor
    ((C.comparison T U g).app H) ((C.comparison T U g).app M)
    ((C.comparison T U g).app N)
    ((C.comparison T U g).app
      ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj (H, M)))
    t t' (S.map e) (R.map (F.map e)) ht
    (by exact ((C.comparison T U g).hom.naturality e).symm)
    _ _ he he'

end WeilConjectures.AdicQbarRealization
