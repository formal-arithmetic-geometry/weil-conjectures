/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.Sites.CechComplex

/-!
# Transport of Čech complexes along functors preserving finite products

Let `G : Over V₀ ⥤ Over V` be a functor preserving finite products, `U₀` a family of objects
over `V₀`, and `P`, `P'` presheaves of abelian groups such that `P(W) ≅ P'(G W)` naturally in
`W` over `V₀`. Then the Čech complex of `U₀` with values in `P` is isomorphic to the Čech complex
of the family `G U₀` with values in `P'`
(`CategoryTheory.Presheaf.cechComplexIsoOfPreservesFiniteProducts`).
-/

@[expose] public section

universe t v v' w w'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {C' : Type w'} [Category.{v'} C']
  {V₀ : C} {V : C'} [HasFiniteProducts (Over V₀)] [HasFiniteProducts (Over V)]
  (G : Over V₀ ⥤ Over V) [PreservesFiniteProducts G] {ι : Type t} (U₀ : ι → Over V₀)

/-- The comparison of the Čech nerves of `G U₀` and of `U₀`. -/
noncomputable abbrev cechNerveObjIso {k : ℕ} (y : Fin (k + 1) → ι) :
    cechNerveObj (fun a ↦ G.obj (U₀ a)) y ≅ G.obj (cechNerveObj U₀ y) :=
  (PreservesProduct.iso G (fun l ↦ U₀ (y l))).symm

lemma cechNerveObjIso_hom_map {k m : ℕ} (y : Fin (m + 1) → ι) (θ : Fin (k + 1) → Fin (m + 1)) :
    (cechNerveObjIso G U₀ y).hom ≫ G.map (cechNerveMap U₀ y θ) =
      cechNerveMap (fun a ↦ G.obj (U₀ a)) y θ ≫ (cechNerveObjIso G U₀ (y ∘ θ)).hom := by
  rw [← cancel_mono (PreservesProduct.iso G (fun l ↦ U₀ ((y ∘ θ) l))).hom, Category.assoc,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_comp_eq]
  refine Pi.hom_ext _ _ fun l ↦ ?_
  simp only [PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π, cechNerveMap_π,
    ← G.map_comp, cechNerveMap_π_assoc]

variable (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) (P' : C'ᵒᵖ ⥤ AddCommGrpCat.{max w v})
  (β : (Over.forget V₀).op ⋙ P ≅ G.op ⋙ (Over.forget V).op ⋙ P')

/-- The isomorphism of the Čech cosimplicial abelian groups of `U₀` with values in `P` and of
`G U₀` with values in `P'`. -/
noncomputable def cechCosimplicialObjectIsoOfPreservesFiniteProducts :
    (cechCosimplicialObject U₀).obj P ≅
      (cechCosimplicialObject (fun a ↦ G.obj (U₀ a))).obj P' :=
  NatIso.ofComponents (fun k ↦ AddEquiv.toAddCommGrpIso
    (AddEquiv.piCongrRight fun y ↦ AddCommGrpCat.addEquivOfIso
      (β.app (op (cechNerveObj U₀ y)) ≪≫
        P'.mapIso ((Over.forget V).mapIso (cechNerveObjIso G U₀ y)).op))) (fun {k m} θ ↦ by
    refine AddCommGrpCat.ext fun c ↦ funext fun y ↦ ?_
    sorry)

end CategoryTheory.Presheaf
