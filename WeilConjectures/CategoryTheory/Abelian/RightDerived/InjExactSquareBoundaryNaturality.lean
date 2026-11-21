/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Naturality of the explicitly defined derived square boundary

Source: Mathlib, HomologicalComplex.HomologySequence.δ_naturality and
InjectiveResolution.isoRightDerivedObj_hom_naturality, following Stacks 01EB.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace CategoryTheory.InjectivelyExactSquare

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- The explicit transported boundary is natural in the object being resolved and in
morphisms of the underived square.

Source: Mathlib, Algebra/Homology/HomologySequenceLemmas.lean,
`HomologicalComplex.HomologySequence.δ_naturality`; CategoryTheory/Abelian/RightDerived.lean,
`InjectiveResolution.isoRightDerivedObj_hom_naturality` and `NatTrans.rightDerived_app_eq`. -/
private noncomputable def resolutionSequenceMap (S : InjectivelyExactSquare.{u, v, w} C)
    {F G : C} (lift : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex) :
    S.resolutionSequence F ⟶ S.resolutionSequence G where
  τ₁ := (S.X₁.mapHomologicalComplex _).map lift
  τ₂ := ((pairFunctor S.X₂ S.X₃).mapHomologicalComplex _).map lift
  τ₃ := (S.X₄.mapHomologicalComplex _).map lift
  comm₁₂ := NatTrans.mapHomologicalComplex_naturality S.diagonal lift
  comm₂₃ := NatTrans.mapHomologicalComplex_naturality S.difference lift

/-- The explicit transported boundary is natural in the object being resolved. -/
theorem boundary_naturality (S : InjectivelyExactSquare.{u, v, w} C) (n : ℕ) {F G : C}
    (f : F ⟶ G) :
    (S.X₄.rightDerived n).map f ≫ S.boundary G n =
      S.boundary F n ≫ (S.X₁.rightDerived (n + 1)).map f := by
  let lift := InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)
  let φ := resolutionSequenceMap (F := F) (G := G) S lift
  have hd := HomologicalComplex.HomologySequence.δ_naturality φ
    (S.resolutionSequence_shortExact F) (S.resolutionSequence_shortExact G)
    n (n + 1) (by simp)
  dsimp [φ, resolutionSequenceMap] at hd
  dsimp [boundary]
  have hzero := InjectiveResolution.desc_commutes_zero f
    (injectiveResolution G) (injectiveResolution F)
  rw [← Category.assoc,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f
      (injectiveResolution F) (injectiveResolution G) lift hzero S.X₄ n]
  simp only [Category.assoc]
  rw [InjectiveResolution.isoRightDerivedObj_inv_naturality f
    (injectiveResolution F) (injectiveResolution G) lift hzero S.X₁ (n + 1)]
  change _ ≫ HomologicalComplex.homologyMap _ _ ≫ _ ≫ _ =
    _ ≫ _ ≫ HomologicalComplex.homologyMap _ _ ≫ _
  rw [← Category.assoc (HomologicalComplex.homologyMap _ _) _ _, ← hd]
  simp only [Category.assoc]

/-- Naturality of the transported boundary under a morphism of injectively exact squares.

Source: Mathlib `HomologicalComplex.HomologySequence.δ_naturality` and
`InjectiveResolution.rightDerived_app_eq`; apply these to the morphism of short exact
resolution sequences induced termwise by the four components of `φ`. -/
theorem boundary_square_naturality (S : InjectivelyExactSquare.{u, v, w} C) (n : ℕ)
    (T : InjectivelyExactSquare.{u, v, w} C) (φ : S.toSquare ⟶ T.toSquare) (F : C) :
    S.boundary F n ≫ (NatTrans.rightDerived φ.τ₁ (n + 1)).app F =
      (NatTrans.rightDerived φ.τ₄ n).app F ≫ T.boundary F n := by
  let τ : pairFunctor S.X₂ S.X₃ ⟶ pairFunctor T.X₂ T.X₃ :=
    { app := fun I ↦ AddCommGrpCat.ofHom ((φ.τ₂.app I).hom.prodMap (φ.τ₃.app I).hom)
      naturality := by
        intro I J f
        ext x
        apply Prod.ext
        · exact congrArg (fun h ↦ h x.1) (φ.τ₂.naturality f)
        · exact congrArg (fun h ↦ h x.2) (φ.τ₃.naturality f) }
  let ψ : S.resolutionSequence F ⟶ T.resolutionSequence F :=
    { τ₁ := (NatTrans.mapHomologicalComplex φ.τ₁ _).app (injectiveResolution F).cocomplex
      τ₂ := (NatTrans.mapHomologicalComplex τ _).app (injectiveResolution F).cocomplex
      τ₃ := (NatTrans.mapHomologicalComplex φ.τ₄ _).app (injectiveResolution F).cocomplex
      comm₁₂ := by
        ext n x
        apply Prod.ext
        · exact congrArg (fun h ↦ h.app ((injectiveResolution F).cocomplex.X n) x)
            φ.comm₁₂.symm
        · exact congrArg (fun h ↦ h.app ((injectiveResolution F).cocomplex.X n) x)
            φ.comm₁₃.symm
      comm₂₃ := by
        ext n x
        symm
        change φ.τ₄.app _ (S.f₂₄.app _ x.1 - S.f₃₄.app _ x.2) =
          T.f₂₄.app _ (φ.τ₂.app _ x.1) - T.f₃₄.app _ (φ.τ₃.app _ x.2)
        rw [map_sub]
        exact congrArg₂ (fun a b ↦ a - b)
          (congrArg (fun h ↦ h.app ((injectiveResolution F).cocomplex.X n) x.1)
            φ.comm₂₄)
          (congrArg (fun h ↦ h.app ((injectiveResolution F).cocomplex.X n) x.2)
            φ.comm₃₄) }
  have hd := HomologicalComplex.HomologySequence.δ_naturality ψ
    (S.resolutionSequence_shortExact F) (T.resolutionSequence_shortExact F)
    n (n + 1) (by simp)
  dsimp [ψ] at hd
  rw [InjectiveResolution.rightDerived_app_eq φ.τ₁ (injectiveResolution F),
    InjectiveResolution.rightDerived_app_eq φ.τ₄ (injectiveResolution F)]
  dsimp [boundary]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change _ ≫ _ ≫ HomologicalComplex.homologyMap _ _ ≫ _ =
    _ ≫ HomologicalComplex.homologyMap _ _ ≫ _ ≫ _
  rw [← Category.assoc _ (HomologicalComplex.homologyMap _ _) _, hd]
  simp only [Category.assoc]

end CategoryTheory.InjectivelyExactSquare
