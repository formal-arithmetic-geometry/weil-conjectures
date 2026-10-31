/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingLeftUnitor

/-! # Unit contraction of the reindexing tensor square

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-reindexing-unit-contraction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe a b c d va vb vc vd
open CategoryTheory CategoryTheory.MonoidalCategory

private theorem tensor_unit_cancel
    {D : Type d} [Category.{vd} D] [MonoidalCategory D]
    {X Y : D} (e : Y ≅ 𝟙_ D) (f g : X ⟶ 𝟙_ D)
    (h : f ⊗ₘ 𝟙 Y = g ⊗ₘ 𝟙 Y) : f = g := by
  have h' : f ⊗ₘ 𝟙 (𝟙_ D) = g ⊗ₘ 𝟙 (𝟙_ D) := by
    apply (cancel_epi (𝟙 X ⊗ₘ e.hom)).mp
    simpa only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id] using
      congrArg (fun k ↦ k ≫ (𝟙 (𝟙_ D) ⊗ₘ e.hom)) h
  apply (cancel_epi (ρ_ X).hom).mp
  simpa only [tensorHom_id, rightUnitor_naturality] using
    congrArg (fun k ↦ k ≫ (ρ_ (𝟙_ D)).hom) h'

private theorem unit_of_tensor_square
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B]
    {C : Type c} [Category.{vc} C] [MonoidalCategory C]
    {D : Type d} [Category.{vd} D] [MonoidalCategory D]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (IA : A) (IB : B)
    (P : B ⥤ A) (J : A ⥤ D) (K : B ⥤ C) (G : C ⥤ D)
    (α : P ⋙ J ≅ K ⋙ G)
    (tA : J.prod J ⋙ tensor D ≅ TA ⋙ J)
    (tB : K.prod K ⋙ tensor C ≅ TB ⋙ K)
    (tG : tensor C ⋙ G ≅ G.prod G ⋙ tensor D)
    (eA : 𝟙_ D ≅ J.obj IA) (eB : 𝟙_ C ≅ K.obj IB)
    (eP : P.obj IB ≅ IA) (eG : G.obj (𝟙_ C) ≅ 𝟙_ D)
    (LA : TA.obj (IA, P.obj IB) ≅ P.obj IB) (LB : TB.obj (IB, IB) ≅ IB)
    (ν : P.obj (TB.obj (IB, IB)) ≅ TA.obj (P.obj IB, P.obj IB))
    (hA : (eA.hom ⊗ₘ 𝟙 (J.obj (P.obj IB))) ≫ tA.hom.app (IA, P.obj IB) ≫ J.map LA.hom =
      (λ_ (J.obj (P.obj IB))).hom)
    (hB : (eB.hom ⊗ₘ 𝟙 (K.obj IB)) ≫ tB.hom.app (IB, IB) ≫ K.map LB.hom =
      (λ_ (K.obj IB)).hom)
    (hP : ν.hom ≫ TA.map (X := (P.obj IB, P.obj IB)) (Y := (IA, P.obj IB))
      (eP.hom, 𝟙 _) ≫ LA.hom = P.map LB.hom)
    (hG : tG.hom.app (𝟙_ C, K.obj IB) ≫ (eG.hom ⊗ₘ 𝟙 (G.obj (K.obj IB))) ≫
      (λ_ (G.obj (K.obj IB))).hom = G.map (λ_ (K.obj IB)).hom)
    (ht : G.map (tB.hom.app (IB, IB)) ≫ α.inv.app (TB.obj (IB, IB)) ≫ J.map ν.hom =
      tG.hom.app (K.obj IB, K.obj IB) ≫
        (α.inv.app IB ⊗ₘ α.inv.app IB) ≫ tA.hom.app (P.obj IB, P.obj IB)) :
    G.map eB.hom ≫ α.inv.app IB ≫ J.map eP.hom = eG.hom ≫ eA.hom := by
  dsimp only [Functor.prod_obj, Functor.comp_obj] at *
  let q : J.obj (P.obj IB) ≅ 𝟙_ D := J.mapIso eP ≪≫ eA.symm
  let z : G.obj (K.obj IB) ≅ 𝟙_ D := (α.app IB).symm ≪≫ q
  have hA' : tA.hom.app (IA, P.obj IB) ≫ J.map LA.hom =
      (eA.inv ⊗ₘ 𝟙 (J.obj (P.obj IB))) ≫ (λ_ (J.obj (P.obj IB))).hom := by
    apply (cancel_epi (eA.hom ⊗ₘ 𝟙 (J.obj (P.obj IB)))).mp
    simpa only [Category.assoc, tensorHom_comp_tensorHom_assoc,
      Iso.hom_inv_id, Category.comp_id, id_tensorHom_id,
      Category.id_comp] using hA
  have hnA := tA.hom.naturality
    (X := (P.obj IB, P.obj IB)) (Y := (IA, P.obj IB)) (eP.hom, 𝟙 _)
  have hnG := tG.hom.naturality
    (X := (𝟙_ C, K.obj IB)) (Y := (K.obj IB, K.obj IB)) (eB.hom, 𝟙 _)
  have hnα := α.inv.naturality LB.hom
  simp only [Functor.comp_map, Functor.prod_map, tensor_map] at hnA hnG
  simp only [J.map_id, G.map_id] at hnA hnG
  simp only [Functor.comp_map] at hnα
  have hz : G.map (λ_ (K.obj IB)).hom ≫ z.hom =
      tG.hom.app (𝟙_ C, K.obj IB) ≫
        ((G.map eB.hom ≫ z.hom) ⊗ₘ 𝟙 (G.obj (K.obj IB))) ≫
        (λ_ (G.obj (K.obj IB))).hom ≫ z.hom := by
    calc
      _ = G.map ((eB.hom ⊗ₘ 𝟙 (K.obj IB)) ≫ tB.hom.app (IB, IB) ≫ K.map LB.hom) ≫
          α.inv.app IB ≫ q.hom := by rw [hB]; rfl
      _ = G.map (eB.hom ⊗ₘ 𝟙 (K.obj IB)) ≫ G.map (tB.hom.app (IB, IB)) ≫
          α.inv.app (TB.obj (IB, IB)) ≫ J.map (P.map LB.hom) ≫ q.hom := by
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% hnα]
      _ = G.map (eB.hom ⊗ₘ 𝟙 (K.obj IB)) ≫
          (G.map (tB.hom.app (IB, IB)) ≫ α.inv.app (TB.obj (IB, IB)) ≫ J.map ν.hom) ≫
          J.map (TA.map (X := (P.obj IB, P.obj IB)) (Y := (IA, P.obj IB))
            (eP.hom, 𝟙 _)) ≫ J.map LA.hom ≫ q.hom := by
        rw [← hP]
        simp only [Functor.map_comp, Category.assoc]
      _ = tG.hom.app (𝟙_ C, K.obj IB) ≫ (G.map eB.hom ⊗ₘ 𝟙 (G.obj (K.obj IB))) ≫
          (α.inv.app IB ⊗ₘ α.inv.app IB) ≫
          (J.map eP.hom ⊗ₘ 𝟙 (J.obj (P.obj IB))) ≫
          tA.hom.app (IA, P.obj IB) ≫ J.map LA.hom ≫ q.hom := by
        rw [ht]
        simp only [Category.assoc]
        rw [← reassoc_of% hnA, reassoc_of% hnG]
      _ = tG.hom.app (𝟙_ C, K.obj IB) ≫
          ((G.map eB.hom ≫ z.hom) ⊗ₘ 𝟙 (G.obj (K.obj IB))) ≫
          (λ_ (G.obj (K.obj IB))).hom ≫ z.hom := by
        have hn : (𝟙 (𝟙_ D) ⊗ₘ α.inv.app IB) ≫
            (λ_ (J.obj (P.obj IB))).hom =
            (λ_ (G.obj (K.obj IB))).hom ≫ α.inv.app IB := by
          simpa only [id_tensorHom, Functor.comp_obj] using leftUnitor_naturality (α.inv.app IB)
        rw [reassoc_of% hA']
        simp only [z, q, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
          Functor.mapIso_hom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
        rw [← reassoc_of% hn]
        simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id]
        simp only [Functor.comp_obj, Functor.prod_obj, Category.id_comp, Category.comp_id]
  have he : G.map eB.hom ≫ z.hom = eG.hom := by
    apply tensor_unit_cancel z _ _
    apply (cancel_mono (λ_ (G.obj (K.obj IB))).hom).mp
    apply (cancel_epi (tG.hom.app (𝟙_ C, K.obj IB))).mp
    apply (cancel_mono z.hom).mp
    rw [← reassoc_of% hG] at hz
    simpa only [Category.assoc] using hz.symm
  have hh := congrArg (fun f ↦ f ≫ eA.hom) he
  simpa only [z, q, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

/-- The specialized tensor square at the coefficient unit. -/
def unitTensorSquare
    (C : FamilyCore l D) (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left) : Prop := by
  letI := (C.data T).units
  letI := (C.data U).units
  exact
    (derivedPull l T.base.left g.hom (C.ring T U g)).map
          ((C.data U).tensor.tensor.hom.app
            (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left,
             pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)) ≫
        (C.comparison T U g).inv.app
          ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj
            (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left,
             pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)) ≫
          (ordinary l T.base.left (C.data T).realization).map
            (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)).hom =
        (C.pullTensor T U g).tensor.hom.app
          ((ordinary l U.base.left (C.data U).realization).obj
            (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left),
           (ordinary l U.base.left (C.data U).realization).obj
            (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)) ≫
          (C.data T).tensor.closed.tensor.map (Prod.mkHom
            ((C.comparison T U g).inv.app
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left))
            ((C.comparison T U g).inv.app
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left))) ≫
          (C.data T).tensor.tensor.hom.app
            ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left),
             (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj
              (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left))

/-- Contract the tensor square at the coefficient unit.
Source: BS Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-reindexing-unit-contraction).

Proof: ordinary reindexing preserves the left unitor by its normalized cochain
representatives. Insert the realization unit maps and the selected canonical
common-stage unit map into the given tensor square. Naturality and the three
left-unit equations identify its two routes with tensoring the two proposed
unit comparisons with the identity. The other tensor factor is isomorphic to
the unit, so the right unitor cancels this tensoring and gives the unit square. -/
theorem reindexing_tensor_unit_contraction
    (C : FamilyCore l D) (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (h_tensor : unitTensorSquare l D C T U g) :
    letI := (C.data T).units
    letI := (C.data U).units
    (derivedPull l T.base.left g.hom (C.ring T U g)).map (C.data U).tensor.unit.hom ≫
      (C.comparison T U g).inv.app (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left) ≫
      (ordinary l T.base.left (C.data T).realization).map
        (C.unit_spec T U g).exists.choose.hom =
    (pullUnit l T.base.left g.hom (C.pullTensor T U g)).hom ≫
      (C.data T).tensor.unit.hom := by
  let := (C.data T).units
  let := (C.data U).units
  let := (C.data T).tensor.closed.monoidal
  let := (C.data U).tensor.closed.monoidal
  exact unit_of_tensor_square
    (commonStageDerivedTensor l (PadicAlgCl l) T.base.left)
    (commonStageDerivedTensor l (PadicAlgCl l) U.base.left)
    (pullbackTensorCommonUnit l (PadicAlgCl l) T.base.left)
    (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)
    (commonStageDerivedPullback l (PadicAlgCl l) g.hom)
    (ordinary l T.base.left (C.data T).realization)
    (ordinary l U.base.left (C.data U).realization)
    (derivedPull l T.base.left g.hom (C.ring T U g))
    (C.comparison T U g) (C.data T).tensor.tensor (C.data U).tensor.tensor
    (C.pullTensor T U g).tensor (C.data T).tensor.unit (C.data U).tensor.unit
    (C.unit_spec T U g).exists.choose (pullUnit l T.base.left g.hom (C.pullTensor T U g))
    (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) T.base.left
      ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj
        (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)))
    (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) U.base.left
      (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left))
    (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom
      (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left)
      (pullbackTensorCommonUnit l (PadicAlgCl l) U.base.left))
    ((C.data T).tensor.left_unit _) ((C.data U).tensor.left_unit _)
    (((C.unit_spec T U g).exists.choose_spec _).1)
    (reindexing_left_unitor l g.hom (C.pullTensor T U g) _) h_tensor

end WeilConjectures.AdicQbarRealization
