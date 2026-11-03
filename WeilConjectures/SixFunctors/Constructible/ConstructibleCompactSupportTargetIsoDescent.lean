/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData

/-! Categorical descent of coherent stage isomorphisms.

This is the formal assembly step for
`(blueprint: lem-sf-constructible-compact-support-target-stage-descent)`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory
namespace WeilConjectures

/-- A coherent family of isomorphisms on the stages of a directed stage system descends to
an isomorphism of the induced pair-category functors.  The geometric construction of the
stage family is deliberately separate from this categorical assembly.
Source: the common-stage representative argument in
`cor-coef-verdier-weil-equivariance.proof.md`, final exceptional-adjunction sentence.
(blueprint: lem-sf-constructible-compact-support-target-stage-descent).
-/
private theorem inverse_naturality {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) {X Y : A} (e : X ≅ Y)
    (a : F.obj X ⟶ G.obj X) (b : F.obj Y ⟶ G.obj Y)
    (h : F.map e.hom ≫ b = a ≫ G.map e.hom) :
    F.map e.inv ≫ a = b ≫ G.map e.inv := by
  apply (cancel_epi (F.map e.hom)).1
  simp only [← Functor.map_comp_assoc, e.hom_inv_id]
  rw [← Category.assoc, h, Category.assoc, ← G.map_comp, e.hom_inv_id,
    G.map_id, Category.comp_id]
  simp only [F.map_id, Category.id_comp]

noncomputable def stageSystem_iso_of_restrictions
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A : I → Type*} [∀ i, Category (A i)]
    (S : StageSystem A) {B : Type*} [Category B]
    (F G : S.PairCategory ⥤ B)
    (e : ∀ i, S.ι i ⋙ F ≅ S.ι i ⋙ G)
    (he : ∀ {i j} (h : i ≤ j) (K : A i),
      F.map ((S.transIso h).inv.app K) ≫
          (e j).hom.app ((S.T h).obj K) =
        (e i).hom.app K ≫
          G.map ((S.transIso h).inv.app K)) :
    F ≅ G := by
  let t : F ≅ G := NatIso.ofComponents
    (fun K ↦ (e K.stage).app K.obj) (by
      intro ⟨i, K⟩ ⟨j, L⟩ f
      obtain ⟨n, hK, hL, a, rfl⟩ :=
        (StageSystem.exists_stage_representation S).2.1 K L f
      have hL' := inverse_naturality F G ((S.transIso hL).symm.app L)
        ((e j).hom.app L) ((e n).hom.app ((S.T hL).obj L)) (he hL L)
      simp only [Iso.app_inv, Iso.symm_inv] at hL'
      change F.map ((S.transIso hK).inv.app K ≫
        (S.ι n).map a ≫ (S.transIso hL).hom.app L) ≫
          (e j).hom.app L =
        (e i).hom.app K ≫
          G.map ((S.transIso hK).inv.app K ≫
            (S.ι n).map a ≫ (S.transIso hL).hom.app L)
      simp only [Functor.map_comp, Category.assoc]
      have hn := (e n).hom.naturality_assoc a
        (G.map ((S.transIso hL).hom.app L))
      simp only [Functor.comp_map] at hn
      rw [hL', hn, ← Category.assoc, he hK K]
      simp only [Category.assoc])
  exact t

end WeilConjectures
