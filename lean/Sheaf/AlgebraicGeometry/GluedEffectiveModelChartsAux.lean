/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.GluedModelStructure

/-!
# Gluing the maps from local effective models

Source: Stacks Project, Descent, Tag 0AP4.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- The gluing construction produces the ambient scheme, charts, and glued map.
(blueprint: lem-pd-glued-effective-model-charts-aux) -/
theorem exists_glued_model_data
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens)
    (hcover : ∀ x : V.left, ∃ i, x ∈ U i)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (W : I → Over Y) (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hinv : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ q i = a.left ≫ q i) :
    ∃ (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left) (j : ∀ i, (W i).left ⟶ W₀.left),
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w) ∧
      (∀ i, j i ≫ W₀.hom = (W i).hom) ∧
      (∀ i, q i ≫ j i = (U i).ι ≫ q₀) := by
  classical
  obtain ⟨W₀, j, hopen, hcover₀, hover, hagree⟩ :=
    exists_glued_model_structure hp D U hcover E hcompat W q hcart hinv
  have hU : TopologicalSpace.IsOpenCover U := by
    change iSup U = ⊤
    apply top_le_iff.mp
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr (hcover x)
  let 𝒰 := V.left.openCoverOfIsOpenCover U hU
  have hf : ∀ i k, pullback.fst (𝒰.f i) (𝒰.f k) ≫ (q i ≫ j i) =
      pullback.snd (𝒰.f i) (𝒰.f k) ≫ (q k ≫ j k) := hagree
  refine ⟨W₀, 𝒰.glueMorphisms (fun i ↦ q i ≫ j i) hf, j,
    hopen, hcover₀, hover, ?_⟩
  intro i
  exact (𝒰.ι_glueMorphisms (fun i ↦ q i ≫ j i) hf i).symm

end CategoryTheory.Over.DescentDatum
