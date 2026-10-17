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
over `V₀`, `U` a family of objects over `V` with isomorphisms `U a ≅ G (U₀ a)`, and `P`, `P'`
presheaves of abelian groups such that `P(W) ≅ P'(G W)` naturally in `W` over `V₀`. Then the
Čech complex of `U₀` with values in `P` is isomorphic to the Čech complex of `U` with values in
`P'` (`CategoryTheory.Presheaf.cechComplexIsoOfPreservesFiniteProducts`).
-/

@[expose] public section

universe t v w

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {C' : Type w} [Category.{v} C']
  {V₀ : C} {V : C'} [HasFiniteProducts (Over V₀)] [HasFiniteProducts (Over V)]
  (G : Over V₀ ⥤ Over V) [PreservesFiniteProducts G] {ι : Type t} (U₀ : ι → Over V₀)
  (U : ι → Over V) (e : ∀ a, U a ≅ G.obj (U₀ a))

/-- The comparison of the Čech nerves of `U` and of `U₀`. -/
noncomputable def cechNerveObjIso {k : ℕ} (y : Fin (k + 1) → ι) :
    cechNerveObj U y ≅ G.obj (cechNerveObj U₀ y) :=
  Pi.mapIso (fun l ↦ e (y l)) ≪≫ (PreservesProduct.iso G (fun l ↦ U₀ (y l))).symm

lemma cechNerveObjIso_hom_map {k m : ℕ} (y : Fin (m + 1) → ι) (θ : Fin (k + 1) → Fin (m + 1)) :
    (cechNerveObjIso G U₀ U e y).hom ≫ G.map (cechNerveMap U₀ y θ) =
      cechNerveMap U y θ ≫ (cechNerveObjIso G U₀ U e (y ∘ θ)).hom := by
  rw [← cancel_mono (PreservesProduct.iso G (fun l ↦ U₀ ((y ∘ θ) l))).hom]
  refine Pi.hom_ext _ _ fun l ↦ ?_
  simp only [cechNerveObjIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, PreservesProduct.iso_hom, piComparison_comp_π, ← G.map_comp]
  have h₁ : cechNerveMap U₀ y θ ≫ Pi.π (fun l ↦ U₀ ((y ∘ θ) l)) l =
      Pi.π (fun l ↦ U₀ (y l)) (θ l) := cechNerveMap_π U₀ y θ l
  rw [h₁, ← piComparison_comp_π, ← PreservesProduct.iso_hom, Iso.inv_hom_id_assoc,
    Pi.mapIso_hom_π, ← piComparison_comp_π, ← PreservesProduct.iso_hom, Iso.inv_hom_id_assoc,
    Pi.mapIso_hom_π]
  exact (cechNerveMap_π_assoc U y θ l _).symm

variable (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) (P' : C'ᵒᵖ ⥤ AddCommGrpCat.{max w v})
  (β : (Over.forget V₀).op ⋙ P ≅ G.op ⋙ (Over.forget V).op ⋙ P')

/-- The isomorphism of the Čech cosimplicial abelian groups of `U₀` with values in `P` and of
`U` with values in `P'`. -/
noncomputable def cechCosimplicialObjectIsoOfPreservesFiniteProducts :
    (cechCosimplicialObject U₀).obj P ≅ (cechCosimplicialObject U).obj P' :=
  NatIso.ofComponents (fun k ↦ AddEquiv.toAddCommGrpIso
    (AddEquiv.piCongrRight fun y ↦ Iso.addCommGroupIsoToAddEquiv
      (β.app (op (cechNerveObj U₀ y)) ≪≫
        P'.mapIso ((Over.forget V).mapIso (cechNerveObjIso G U₀ U e y)).op))) (fun {k m} θ ↦ by
    refine AddCommGrpCat.ext fun c ↦ funext fun y ↦ ?_
    have key : (cechNerveObjIso G U₀ U e y).hom.left ≫
          (G.map (cechNerveMap U₀ y θ.toOrderHom)).left =
        (cechNerveMap U y θ.toOrderHom).left ≫
          (cechNerveObjIso G U₀ U e (y ∘ θ.toOrderHom)).hom.left := by
      rw [← Over.comp_left, ← Over.comp_left, cechNerveObjIso_hom_map]
    have h₁ : β.hom.app (op (cechNerveObj U₀ y))
        (P.map (cechNerveMap U₀ y θ.toOrderHom).left.op (c (y ∘ θ.toOrderHom))) =
        P'.map (G.map (cechNerveMap U₀ y θ.toOrderHom)).left.op
          (β.hom.app (op (cechNerveObj U₀ (y ∘ θ.toOrderHom))) (c (y ∘ θ.toOrderHom))) :=
      ConcreteCategory.congr_hom (β.hom.naturality (cechNerveMap U₀ y θ.toOrderHom).op)
        (c (y ∘ θ.toOrderHom))
    change P'.map (cechNerveObjIso G U₀ U e y).hom.left.op
        (β.hom.app (op (cechNerveObj U₀ y))
          (P.map (cechNerveMap U₀ y θ.toOrderHom).left.op (c (y ∘ θ.toOrderHom)))) =
      P'.map (cechNerveMap U y θ.toOrderHom).left.op
        (P'.map (cechNerveObjIso G U₀ U e (y ∘ θ.toOrderHom)).hom.left.op
          (β.hom.app (op (cechNerveObj U₀ (y ∘ θ.toOrderHom))) (c (y ∘ θ.toOrderHom))))
    erw [h₁]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← P'.map_comp,
      ← P'.map_comp, ← op_comp, ← op_comp, key])

/-- The Čech complex of `U₀` with values in `P` is isomorphic to the Čech complex of `U` with
values in `P'`. -/
noncomputable def cechComplexIsoOfPreservesFiniteProducts :
    (cechComplex U₀).obj P ≅ (cechComplex U).obj P' :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
    (cechCosimplicialObjectIsoOfPreservesFiniteProducts G U₀ U e P P' β)

include G e β in
/-- Exactness of Čech complexes transfers along `CategoryTheory.Presheaf.cechComplexIsoOfPreservesFiniteProducts`. -/
lemma exactAt_cechComplex_of_preservesFiniteProducts (q : ℕ)
    (h : ((cechComplex U₀).obj P).ExactAt q) : ((cechComplex U).obj P').ExactAt q :=
  h.of_iso (cechComplexIsoOfPreservesFiniteProducts G U₀ U e P P' β)

end CategoryTheory.Presheaf
