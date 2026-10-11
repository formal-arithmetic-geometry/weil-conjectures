/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.Sites.CechComplex

/-!
# Čech complexes of families transported along a functor

Let `Φ : C' ⥤ C` be a functor and `Ψ : Over V' ⥤ Over V` a functor preserving finite products
which lies over `Φ`, in the sense of a natural isomorphism `Ψ ⋙ Over.forget V ≅ Over.forget V' ⋙ Φ`
(for instance `Over.post Φ` for a functor `Φ` preserving finite limits). For a family
`U : ι → Over V'` and a presheaf `P` of abelian groups on `C`, the Čech complex of `P` on the
family `Ψ ∘ U` is isomorphic to the Čech complex of `Φᵒᵖ ⋙ P` on `U`: the members
`Ψ (U (y 0)) ×_V ⋯ ×_V Ψ (U (y k))` of the Čech nerve of `Ψ ∘ U` are the images under `Φ` of the
members of the Čech nerve of `U`.

## Main statements

- `CategoryTheory.Presheaf.cechComplexMapIso`: the isomorphism of Čech complexes.
- `CategoryTheory.Presheaf.exactAt_cechComplex_map_iff`: exactness of the Čech complexes agrees.
-/

@[expose] public section

universe t v w

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {C' : Type w} [Category.{v} C'] {V : C} {V' : C'}
  [HasFiniteProducts (Over V)] [HasFiniteProducts (Over V')]
  (Φ : C' ⥤ C) (Ψ : Over V' ⥤ Over V) [PreservesFiniteProducts Ψ]
  (e : Ψ ⋙ Over.forget V ≅ Over.forget V' ⋙ Φ) {ι : Type t} (U : ι → Over V')

/-- The identification of a member of the Čech nerve of `Ψ ∘ U` with the image under `Φ` of the
corresponding member of the Čech nerve of `U`. -/
noncomputable def cechNerveObjMapIso {k : ℕ} (y : Fin (k + 1) → ι) :
    (cechNerveObj (fun a ↦ Ψ.obj (U a)) y).left ≅ Φ.obj (cechNerveObj U y).left :=
  (Over.forget V).mapIso (PreservesProduct.iso Ψ (fun l ↦ U (y l))).symm ≪≫
    e.app (cechNerveObj U y)

lemma cechNerveMap_map {k m : ℕ} (y : Fin (m + 1) → ι) (θ : Fin (k + 1) → Fin (m + 1)) :
    (PreservesProduct.iso Ψ (fun l ↦ U (y l))).inv ≫ Ψ.map (cechNerveMap U y θ) =
      cechNerveMap (fun a ↦ Ψ.obj (U a)) y θ ≫
        (PreservesProduct.iso Ψ (fun l ↦ U ((y ∘ θ) l))).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine Pi.hom_ext _ _ fun l ↦ ?_
  have h₁ : Ψ.map (cechNerveMap U y θ) ≫ piComparison Ψ (fun l ↦ U ((y ∘ θ) l)) ≫
      Pi.π (fun l ↦ Ψ.obj (U ((y ∘ θ) l))) l = Ψ.map (Pi.π (fun l ↦ U (y l)) (θ l)) := by
    rw [piComparison_comp_π, ← Ψ.map_comp]
    erw [cechNerveMap_π]
  have h₂ : piComparison Ψ (fun l ↦ U (y l)) ≫ cechNerveMap (fun a ↦ Ψ.obj (U a)) y θ ≫
      Pi.π (fun l ↦ Ψ.obj (U ((y ∘ θ) l))) l = Ψ.map (Pi.π (fun l ↦ U (y l)) (θ l)) := by
    erw [cechNerveMap_π]
    rw [piComparison_comp_π]
  simp only [PreservesProduct.iso_hom, Category.assoc]
  exact h₁.trans h₂.symm

lemma cechNerveObjMapIso_naturality {k m : ℕ} (y : Fin (m + 1) → ι)
    (θ : Fin (k + 1) → Fin (m + 1)) :
    (cechNerveMap (fun a ↦ Ψ.obj (U a)) y θ).left ≫ (cechNerveObjMapIso Φ Ψ e U (y ∘ θ)).hom =
      (cechNerveObjMapIso Φ Ψ e U y).hom ≫ Φ.map (cechNerveMap U y θ).left := by
  have h := congrArg CommaMorphism.left (cechNerveMap_map Ψ U y θ)
  simp only [Over.comp_left] at h
  have h' := e.hom.naturality (cechNerveMap U y θ)
  simp only [Functor.comp_map, Over.forget_map] at h'
  simp only [cechNerveObjMapIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Over.forget_map, Iso.app_hom, Category.assoc]
  rw [← reassoc_of% h, h']

variable (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})

/-- The isomorphism between the Čech cosimplicial objects of `P` on `Ψ ∘ U` and of `Φᵒᵖ ⋙ P` on
`U`. -/
noncomputable def cechCosimplicialObjectMapIso :
    (cechCosimplicialObject (fun a ↦ Ψ.obj (U a))).obj P ≅
      (cechCosimplicialObject U).obj (Φ.op ⋙ P) :=
  NatIso.ofComponents
    (fun k ↦ AddEquiv.toAddCommGrpIso (AddEquiv.piCongrRight fun y ↦
      (P.mapIso (cechNerveObjMapIso Φ Ψ e U y).symm.op).addCommGroupIsoToAddEquiv))
    (fun {k m} θ ↦ by
      refine AddCommGrpCat.ext fun c ↦ funext fun y ↦ ?_
      change P.map (cechNerveObjMapIso Φ Ψ e U y).inv.op
          (P.map (cechNerveMap (fun a ↦ Ψ.obj (U a)) y θ.toOrderHom).left.op
            (c (y ∘ θ.toOrderHom))) =
        P.map (Φ.map (cechNerveMap U y θ.toOrderHom).left).op
          (P.map (cechNerveObjMapIso Φ Ψ e U (y ∘ θ.toOrderHom)).inv.op (c (y ∘ θ.toOrderHom)))
      have key : (cechNerveObjMapIso Φ Ψ e U y).inv ≫
          (cechNerveMap (fun a ↦ Ψ.obj (U a)) y θ.toOrderHom).left =
          Φ.map (cechNerveMap U y θ.toOrderHom).left ≫
            (cechNerveObjMapIso Φ Ψ e U (y ∘ θ.toOrderHom)).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
        exact cechNerveObjMapIso_naturality Φ Ψ e U y θ.toOrderHom
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← P.map_comp,
        ← P.map_comp, ← op_comp, ← op_comp, key])

/-- **The Čech complex of a transported family.** The Čech complex of `P` on `Ψ ∘ U` is
isomorphic to the Čech complex of `Φᵒᵖ ⋙ P` on `U`. -/
noncomputable def cechComplexMapIso :
    (cechComplex (fun a ↦ Ψ.obj (U a))).obj P ≅ (cechComplex U).obj (Φ.op ⋙ P) :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
    (cechCosimplicialObjectMapIso Φ Ψ e U P)

include e in
lemma exactAt_cechComplex_map_iff (q : ℕ) :
    ((cechComplex (fun a ↦ Ψ.obj (U a))).obj P).ExactAt q ↔
      ((cechComplex U).obj (Φ.op ⋙ P)).ExactAt q :=
  ⟨fun h ↦ h.of_iso (cechComplexMapIso Φ Ψ e U P),
    fun h ↦ h.of_iso (cechComplexMapIso Φ Ψ e U P).symm⟩

end CategoryTheory.Presheaf
