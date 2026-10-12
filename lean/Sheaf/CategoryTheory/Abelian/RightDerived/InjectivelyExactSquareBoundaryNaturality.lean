/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare
import Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquareBoundarySquareNaturality
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Naturality of the explicitly defined derived square boundary

Source: Mathlib, HomologicalComplex.HomologySequence.δ_naturality and
InjectiveResolution.isoRightDerivedObj_hom_naturality, following Stacks 01EB.
(blueprint: lem-sc-injectively-exact-square-boundary-naturality).
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
`InjectiveResolution.isoRightDerivedObj_hom_naturality` and `NatTrans.rightDerived_app_eq`.
(blueprint: lem-sc-injectively-exact-square-boundary-naturality).

Proof: For a morphism F -> G lift it to a cochain map between the chosen injective
resolutions, extending the morphism on their augmentations. Applying the four additive
functors and their natural edge transformations gives a morphism of `resolutionSequence F`
to `resolutionSequence G`: the middle component applies the two middle functors to the
lift and takes their product. The two commutation conditions are the naturality of the
four edges. Apply complex connecting-map naturality to these short exact sequences.
Transport the resulting equality through the four resolution comparisons. The comparison
naturality theorem identifies the maps induced by the lift with the canonical derived
functor maps, and cancellation of the comparison isomorphisms gives the first assertion.
For a morphism of squares S -> T use the same chosen resolution of F for both squares.
Apply its four vertex transformations termwise; their edge commutation relations give a
morphism of the two resolution short exact sequences. Complex connecting-map naturality
again applies. Now NatTrans.rightDerived_app_eq identifies the two outer maps after
transport with the components of the derived outer vertex transformations. Cancellation
of the comparisons gives the second assertion. Both assertions concern the same explicit
`boundary` definition, so there is no independent choice of connecting maps to reconcile. -/
private noncomputable def resolutionSequenceMap (S : InjectivelyExactSquare.{u, v, w} C)
    {F G : C} (lift : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex) :
    S.resolutionSequence F ⟶ S.resolutionSequence G where
  τ₁ := (S.X₁.mapHomologicalComplex _).map lift
  τ₂ := ((pairFunctor S.X₂ S.X₃).mapHomologicalComplex _).map lift
  τ₃ := (S.X₄.mapHomologicalComplex _).map lift
  comm₁₂ := NatTrans.mapHomologicalComplex_naturality S.diagonal lift
  comm₂₃ := NatTrans.mapHomologicalComplex_naturality S.difference lift

private theorem boundary_object_naturality (S : InjectivelyExactSquare.{u, v, w} C) (n : ℕ) :
    ∀ {F G : C} (f : F ⟶ G),
      (S.X₄.rightDerived n).map f ≫ S.boundary G n =
        S.boundary F n ≫ (S.X₁.rightDerived (n + 1)).map f := by
  intro F G f
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

theorem boundary_naturality (S : InjectivelyExactSquare.{u, v, w} C) (n : ℕ) :
    (∀ {F G : C} (f : F ⟶ G),
      (S.X₄.rightDerived n).map f ≫ S.boundary G n =
        S.boundary F n ≫ (S.X₁.rightDerived (n + 1)).map f) ∧
    (∀ (T : InjectivelyExactSquare.{u, v, w} C) (φ : S.toSquare ⟶ T.toSquare) (F : C),
      S.boundary F n ≫ (NatTrans.rightDerived φ.τ₁ (n + 1)).app F =
        (NatTrans.rightDerived φ.τ₄ n).app F ≫ T.boundary F n) := by
  exact ⟨S.boundary_object_naturality n, boundary_square_naturality S n⟩

end CategoryTheory.InjectivelyExactSquare
