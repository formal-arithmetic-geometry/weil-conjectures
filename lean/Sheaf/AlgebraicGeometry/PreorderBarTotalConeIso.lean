/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarTotalCone
import Sheaf.AlgebraicGeometry.PreorderBarTotalConeDifferential

/-! # The explicit total-cone cochain isomorphism

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] {A : Type w} [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A] [HasCoproducts.{u} A] [HasCoproducts.{0} A]
  {D E : I ⥤ CochainComplex A ℤ} (φ : D ⟶ E)

/-- The explicit total-cone cochain isomorphism.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-preorder-bar-total-cone-iso).

Proof: Apply HomologicalComplex.Hom.isoOfComponents to coneTotalXIso. Its compatibility field is
exactly
coneTotalXHom_comm. Thus its object data comes from the explicit mutually inverse degreewise maps,
and its proof field comes from the proved differential identity. -/
noncomputable def totalConeIso :
    total (coneDiagram φ) ≅ CochainComplex.mappingCone (totalArrow φ) :=
  HomologicalComplex.Hom.isoOfComponents (coneTotalXIso φ) (by
    intro n m h
    obtain rfl : m = n + 1 := h.symm
    exact coneTotalXHom_comm φ n)

omit [HasBinaryBiproducts A] in
lemma totalArrow_augmentation (c : Cocone D) (e : Cocone E) (f : c.pt ⟶ e.pt)
    (hf : ∀ i, φ.app i ≫ e.ι.app i = c.ι.app i ≫ f) :
    totalArrow φ ≫ totalAugmentation E e = totalAugmentation D c ≫ f :=
  totalAugmentation_naturality D E OrderHom.id c e (sameIndexMap φ) f hf

omit [HasBinaryBiproducts A] in
@[reassoc]
lemma ιTerm_totalAugmentation_zero (c : Cocone D) (q : ℤ) (σ : Fin 1 →o I) :
    ιTerm D 0 q q (by simp) σ ≫ (totalAugmentation D c).f q = (c.ι.app (σ 0)).f q := by
  let F := HomologicalComplex.eval A (ComplexShape.up ℤ) q
  simp only [ιTerm, totalAugmentation, HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex₂.ιTotal_map_assoc, collapse,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
  change Sigma.ι _ σ ≫ (columnXIso D 0 q).inv ≫
    F.map ((augmentation D c).app (op ⦋0⦌)) ≫ _ = _
  change Sigma.ι (fun σ : Fin 1 →o I ↦ F.obj (D.obj (σ 0))) σ ≫
    sigmaComparison F (fun σ : Fin 1 →o I ↦ D.obj (σ 0)) ≫
      F.map ((augmentation D c).app (op ⦋0⦌)) ≫
        (singleColumn c.pt).ιTotal (ComplexShape.up ℤ) 0 q q (by
          change q - (0 : ℕ) = q; simp) ≫
          collapseX c.pt q = _
  rw [ι_comp_sigmaComparison_assoc, ← F.map_comp_assoc]
  simp only [augmentation, Sigma.ι_desc]
  simp only [ι_collapseX, eqToHom_refl]
  exact Category.comp_id _

omit [HasBinaryBiproducts A] in
@[reassoc]
lemma ιTerm_totalAugmentation_succ (c : Cocone D) (p : ℕ) (q n : ℤ)
    (h : q - ((p + 1 : ℕ) : ℤ) = n) (σ : Fin (p + 1 + 1) →o I) :
    ιTerm D (p + 1) q n h σ ≫ (totalAugmentation D c).f n = 0 := by
  simp only [ιTerm, totalAugmentation, HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex₂.ιTotal_map_assoc]
  have hz : IsZero ((singleColumn c.pt).X (p + 1)) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 c.pt (p + 1) (by omega)
  have hz' := (HomologicalComplex.eval A (ComplexShape.up ℤ) q).map_isZero hz
  rw [hz'.eq_of_tgt
    (((AlgebraicTopology.AlternatingFaceMapComplex.ε.app (augmented D c)).f (p + 1)).f q) 0]
  simp

/-- Total-cone comparison preserves canonical augmentation.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-total-cone-augmentation).

Proof: First prove that totalArrow commutes with augmentation by the general reindexing naturality
theorem. Test the claimed cone equality on each bar generator and both cone inclusions. In
horizontal degree zero the total augmentation is the cocone map on the coefficient, and the source
comparison sign is 1. Both sides are then the same mappingCone.map. In positive horizontal degree
the augmentation is zero, as follows from the zero component of the single column. These two cases
prove the exact augmentation equality. -/
lemma totalConeIso_augmentation (c : Cocone D) (e : Cocone E) (f : c.pt ⟶ e.pt)
    (hf : ∀ i, φ.app i ≫ e.ι.app i = c.ι.app i ≫ f) :
    (totalConeIso φ).hom ≫ CochainComplex.mappingCone.map (totalArrow φ) f
      (totalAugmentation D c) (totalAugmentation E e)
      (totalArrow_augmentation φ c e f hf) =
    totalAugmentation (coneDiagram φ) (coneCocone φ c e f hf) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ιTerm_hom_ext (coneDiagram φ) n
  intro p q h σ
  apply CochainComplex.mappingCone.ext_from (φ.app (σ 0)) (q + 1) q rfl
  · cases p with
    | zero =>
      have hq : q = n := by simpa using h
      subst q
      simp [totalConeIso, coneTotalXIso, Category.assoc, CochainComplex.mappingCone.map,
        ιTerm_totalAugmentation_zero, ιTerm_totalAugmentation_zero_assoc, coneCocone]
    | succ p =>
      simp [totalConeIso, coneTotalXIso, Category.assoc, CochainComplex.mappingCone.map,
        ιTerm_totalAugmentation_succ, ιTerm_totalAugmentation_succ_assoc]
  · cases p with
    | zero =>
      have hq : q = n := by simpa using h
      subst q
      simp [totalConeIso, coneTotalXIso, Category.assoc, CochainComplex.mappingCone.map,
        ιTerm_totalAugmentation_zero, ιTerm_totalAugmentation_zero_assoc, coneCocone]
    | succ p =>
      simp [totalConeIso, coneTotalXIso, Category.assoc, CochainComplex.mappingCone.map,
        ιTerm_totalAugmentation_succ, ιTerm_totalAugmentation_succ_assoc]

end CategoryTheory.PreorderBar
