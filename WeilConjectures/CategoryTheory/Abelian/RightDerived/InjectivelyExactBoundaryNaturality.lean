/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare
import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section

universe u v w
open CategoryTheory
namespace CategoryTheory.InjectivelyExactSquare
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- Naturality of the transported boundary under a morphism of injectively exact squares.

Source: Mathlib `HomologicalComplex.HomologySequence.δ_naturality` and
`InjectiveResolution.rightDerived_app_eq`; apply these to the morphism of short exact
resolution sequences induced termwise by the four components of `φ`.
(blueprint: lem-sc-injectively-exact-square-boundary-square-naturality). -/
theorem boundary_square_naturality (S : InjectivelyExactSquare.{u, v, w} C) (n : ℕ) :
    ∀ (T : InjectivelyExactSquare.{u, v, w} C) (φ : S.toSquare ⟶ T.toSquare) (F : C),
      S.boundary F n ≫ (NatTrans.rightDerived φ.τ₁ (n + 1)).app F =
        (NatTrans.rightDerived φ.τ₄ n).app F ≫ T.boundary F n := by
  intro T φ F
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
