/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.PreorderBarTotal
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-! # Degreewise splittings of bar inclusions

Source: the full-subdiagram bar-inclusion paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-total-split).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace CategoryTheory.PreorderBar

private lemma sigma_desc_split {C : Type w} [Category.{v} C] [HasZeroMorphisms C]
    {I J : Type u} (M : I → C) (N : J → C) [HasCoproduct M] [HasCoproduct N]
    (f : I → J) (hf : Function.Injective f) (g : ∀ i : I, M i ⟶ N (f i))
    [∀ i : I, IsSplitMono (g i)] :
    IsSplitMono (Sigma.desc (fun i ↦ g i ≫ Sigma.ι N (f i))) := by
  classical
  let r : ∐ N ⟶ ∐ M := Sigma.desc (fun j ↦ if h : j ∈ Set.range f then
    eqToHom (congrArg N h.choose_spec.symm) ≫ retraction (g h.choose) ≫
      Sigma.ι M h.choose else 0)
  refine IsSplitMono.mk' ⟨r, ?_⟩
  apply Sigma.hom_ext
  intro i
  have h : f i ∈ Set.range f := ⟨i, rfl⟩
  have hi : h.choose = i := hf h.choose_spec
  simp only [Sigma.ι_desc_assoc, r, Category.assoc, Sigma.ι_desc, dif_pos h]
  simp [hi]

variable {I J : Type u} [Preorder I] [Preorder J]
  {C : Type w} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasCoproducts.{u} C] [HasCoproducts.{0} C]

private lemma string_injective (f : I →o J) (hf : Function.Injective f) (p : ℕ) :
    Function.Injective (fun σ : Fin (p + 1) →o I ↦ f.comp σ) := by
  intro σ τ h
  ext i
  exact hf (congrArg (fun x : Fin (p + 1) →o J ↦ x i) h)

omit [HasZeroObject C] [HasCoproducts.{0} C] in
set_option backward.isDefEq.respectTransparency false in
lemma columnMap_naturality
    (D : I ⥤ CochainComplex C ℤ) (E : J ⥤ CochainComplex C ℤ)
    (f : I →o J) (φ : D ⟶ orderFunctor f ⋙ E) (p : ℕ) (q : ℤ) :
    ((AlgebraicTopology.AlternatingFaceMapComplex.map (reindex D E f φ)).f p).f q ≫
        (columnXIso E p q).hom =
      (columnXIso D p q).hom ≫ Sigma.desc (fun σ : Fin (p + 1) →o I ↦
        (φ.app (σ 0)).f q ≫
          Sigma.ι (fun τ : Fin (p + 1) →o J ↦ (E.obj (τ 0)).X q) (f.comp σ)) := by
  let F := HomologicalComplex.eval C (ComplexShape.up ℤ) q
  apply (cancel_epi (columnXIso D p q).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply Sigma.hom_ext
  intro σ
  change Sigma.ι _ σ ≫ (PreservesCoproduct.iso F _).inv ≫
    F.map ((reindex D E f φ).app (op ⦋p⦌)) ≫ (PreservesCoproduct.iso F _).hom = _
  simp only [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc]
  rw [← F.map_comp_assoc]
  simp only [reindex, Sigma.ι_desc]
  rw [F.map_comp, Category.assoc]
  have h : (PreservesCoproduct.iso F (fun τ : Fin (p + 1) →o J ↦ E.obj (τ 0))).hom =
      inv (sigmaComparison F (fun τ : Fin (p + 1) →o J ↦ E.obj (τ 0))) := by
    change (PreservesCoproduct.iso F _).hom = inv (PreservesCoproduct.iso F _).inv
    exact (IsIso.Iso.inv_inv _).symm
  rw [h, map_ι_comp_inv_sigmaComparison]
  rfl

omit [HasZeroObject C] in
/-- A total bar map acts on a labelled generator by its coefficient map. -/
lemma ιTerm_map
    (D : I ⥤ CochainComplex C ℤ) (E : J ⥤ CochainComplex C ℤ)
    (f : I →o J) (φ : D ⟶ orderFunctor f ⋙ E)
    (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n) (σ : Fin (p + 1) →o I) :
    ιTerm D p q n h σ ≫ (totalMap D E f φ).f n =
      (φ.app (σ 0)).f q ≫ ιTerm E p q n h (f.comp σ) := by
  let ψ := AlgebraicTopology.AlternatingFaceMapComplex.map (reindex D E f φ)
  have hh : Sigma.ι (fun τ : Fin (p + 1) →o I ↦ (D.obj (τ 0)).X q) σ ≫
      (columnXIso D p q).inv ≫ (ψ.f p).f q =
      (φ.app (σ 0)).f q ≫
        Sigma.ι (fun τ : Fin (p + 1) →o J ↦ (E.obj (τ 0)).X q) (f.comp σ) ≫
          (columnXIso E p q).inv := by
    apply (cancel_mono (columnXIso E p q).hom).1
    rw [Category.assoc, Category.assoc, columnMap_naturality D E f φ p q]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_desc,
      Iso.inv_hom_id, Category.comp_id]
  dsimp only [ιTerm, totalMap]
  simp only [Category.assoc, HomologicalComplex₂.ιTotal_map]
  simpa only [Category.assoc, ψ, bicomplex] using
    congrArg (fun k ↦ k ≫ (bicomplex E).ιTotal (ComplexShape.up ℤ) p q n h) hh

omit [HasZeroObject C] in
/-- Injective reindexing with degreewise split coefficients gives a split bar-total map.

Source: the full-subdiagram bar-inclusion paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-total-split).

Proof: An injective order map induces an injection on finite monotone strings.
At each bar degree, retract the included summands using the given coefficient
retractions and send all other summands to zero. Evaluation of complexes preserves
these coproducts. Retract the total map separately on every diagonal summand.
No compatibility of the retractions with differentials is asserted or needed. -/
theorem totalMap_split
    (D : I ⥤ CochainComplex C ℤ) (E : J ⥤ CochainComplex C ℤ)
    (f : I →o J) (hf : Function.Injective f) (φ : D ⟶ orderFunctor f ⋙ E)
    (hφ : ∀ (i : I) (q : ℤ), IsSplitMono ((φ.app i).f q)) (n : ℤ) :
    IsSplitMono ((totalMap D E f φ).f n) := by
  let ψ := AlgebraicTopology.AlternatingFaceMapComplex.map (reindex D E f φ)
  have hs (p : ℕ) (q : ℤ) : IsSplitMono ((ψ.f p).f q) := by
    let := hφ
    let g (σ : Fin (p + 1) →o I) := (φ.app (σ 0)).f q
    let h := sigma_desc_split (fun σ : Fin (p + 1) →o I ↦ (D.obj (σ 0)).X q)
      (fun τ : Fin (p + 1) →o J ↦ (E.obj (τ 0)).X q)
      (fun σ ↦ f.comp σ) (string_injective f hf p) g
    have he := columnMap_naturality D E f φ p q
    refine IsSplitMono.mk' ⟨(columnXIso E p q).hom ≫
      @retraction _ _ _ _ _ h ≫ (columnXIso D p q).inv, ?_⟩
    rw [← Category.assoc, ← Category.assoc, he]
    simp [g, Category.assoc]
  let r : ((bicomplex E).total (ComplexShape.up ℤ)).X n ⟶
      ((bicomplex D).total (ComplexShape.up ℤ)).X n :=
    (bicomplex E).totalDesc (fun p q h ↦
      @retraction _ _ _ _ ((ψ.f p).f q) (hs p q) ≫
        (bicomplex D).ιTotal (ComplexShape.up ℤ) p q n h)
  refine IsSplitMono.mk' ⟨r, ?_⟩
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  simp only [totalMap, HomologicalComplex₂.ιTotal_map_assoc]
  change (ψ.f p).f q ≫ (bicomplex E).ιTotal (ComplexShape.up ℤ) p q n h ≫ r =
    (bicomplex D).ιTotal (ComplexShape.up ℤ) p q n h ≫ 𝟙 _
  simp only [r, HomologicalComplex₂.ι_totalDesc]
  let := hs p q
  simp

end CategoryTheory.PreorderBar
