/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification

/-! # Tensoring the compactification graph transfer

Source: steps 3--4 of `lem-sf-etale-graph-unit-tensor`; Stacks Tag 0GL1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance] Sheaf.monoidalCategory

private theorem identity_tensor
    {C : Type*} [Category* C] [MonoidalCategory C]
    (F : C ⥤ C) (ε : F ≅ 𝟭 C) (c : F ≅ F ⋙ F)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (hc : ∀ X, c.hom.app X ≫ F.map (ε.hom.app X) = 𝟙 _)
    (hδ : ∀ X Y, (δ.hom.app X).app Y ≫ (c.hom.app X ⊗ₘ c.hom.app Y) =
      c.hom.app (X ⊗ Y) ≫ F.map ((δ.hom.app X).app Y) ≫
        (δ.hom.app (F.obj X)).app (F.obj Y))
    (X Y : C) :
    (δ.hom.app X).app Y ≫ (ε.hom.app X ⊗ₘ ε.hom.app Y) = ε.hom.app (X ⊗ Y) := by
  have hf := (Functor.FullyFaithful.id C).ofIso ε.symm
  have := hf.faithful
  apply F.map_injective
  apply (cancel_epi (c.hom.app (X ⊗ Y))).mp
  apply (cancel_mono ((δ.hom.app X).app Y)).mp
  have hn : (δ.hom.app (F.obj X)).app (F.obj Y) ≫
      (F.map (ε.hom.app X) ⊗ₘ F.map (ε.hom.app Y)) =
      F.map (ε.hom.app X ⊗ₘ ε.hom.app Y) ≫ (δ.hom.app X).app Y := by
    have hn₁ := NatTrans.congr_app (δ.hom.naturality (ε.hom.app X)) (F.obj Y)
    have hn₂ := (δ.hom.app X).naturality (ε.hom.app Y)
    dsimp at hn₁ hn₂
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def,
      F.map_comp, Category.assoc, ← reassoc_of% hn₁]
    dsimp only [Functor.id_obj]
    rw [← hn₂]
  simp only [F.map_comp, Category.assoc]
  rw [← hn, ← reassoc_of% (hδ X Y), reassoc_of% (hc (X ⊗ Y))]
  simp only [tensorHom_comp_tensorHom, hc, id_tensorHom_id]
  exact Category.comp_id _

private theorem identity_pullback_tensor
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M N : DerivedCategoryModule A X) :
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (𝟙 X) M N).hom ≫
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app M ⊗ₘ
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app N) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app (M ⊗ N) := by
  exact identity_tensor _ (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.comp_id _).symm)
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) (𝟙 X))
    (leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) (𝟙 X))
    (leftDerivedUpperStarTensorComparison_comp (ModuleCat.{u + 1} A)
      (𝟙 X) (𝟙 X) (𝟙 X) (Category.comp_id _).symm) M N

private theorem section_tensor
    (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (s : V ⟶ T) (p : T ⟶ V) (h : s ≫ p = 𝟙 V)
    (M N : DerivedCategoryModule A V) :
    L((s)^*[ModuleCat.{u + 1} A]).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) p M N).hom ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) s
        (L((p)^*[ModuleCat.{u + 1} A]).obj M)
        (L((p)^*[ModuleCat.{u + 1} A]).obj N)).hom ≫
      ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app M ⊗ₘ
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app N) =
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app
        (M ⊗ N) := by
  have hc := leftDerivedUpperStarTensorComparison_comp (ModuleCat.{u + 1} A)
    s p (𝟙 V) h.symm M N
  simp only [← leftDerivedUpperStarTensorIso_hom] at hc
  apply (cancel_epi
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s p (𝟙 V) h.symm).hom.app
      (M ⊗ N))).mp
  simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [← reassoc_of% hc]
  simp only [tensorHom_comp_tensorHom, Iso.hom_inv_id_app_assoc]
  exact identity_pullback_tensor A V M N

/-- Pull back the open projection comparison to the self-base-change square.
The second tensor factor is identified by the specified inverse-image square and
exact/left-derived comparison. Source: Stacks Tags 0GL1 and 0E48
(auxiliary; not a blueprint node). -/
/-- The graph isomorphism is monoidal after the section and open projection comparisons.
This is the coherence calculation for pullback composition, the open projection mate, and
exact coefficient change. Source: Stacks Tag 0GL1, blueprint node
`lem-sf-etale-graph-transfer-tensor` step 4. -/
/-- Tensor compatibility of graph transfer, before applying the proper direct image.
Source: `lem-sf-etale-graph-unit-tensor`, steps 2--4; Stacks Tags 015F and 0GL1
(auxiliary; not a blueprint node).

Proof in words. The self graph is clopen by the existing graph geometry. For a
clopen immersion, restriction is both left and right adjoint to extension by zero.
The counit of the first adjunction is the inverse unit of the second. Transposing
the tensor projection comparison therefore identifies the two adjoint projection
maps as inverses. Their unit and counit equations and naturality show that tensoring
a transfer is the transfer of the restricted tensor map, with pullback tensor
comparisons inserted. Normalize the graph isomorphism using monoidality of the
section and composition comparisons, the defining open-projection unit equation,
and associativity and identity laws for the coefficient square. Apply transfer to
this normalization and use its naturality at both ends. All calculations use the
specified comparisons. No clopen derived-product construction, boundedness, or
quasi-compactness hypothesis is needed; empty schemes and the zero ring satisfy
the same categorical equations. -/
end AlgebraicGeometry.Etale
