/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFunctor

/-! # Transition comparison component for the common-stage dual

Source: thm-coef-qbar-verdier, tower-coherence paragraph.
(blueprint: lem-coef-qbar-verdier-comparison-component)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w a b c d
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace CategoryTheory.StageSystem

private theorem transition_square
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type a} [∀ i, Category.{b} (C i)]
    {D : I → Type c} [∀ i, Category.{d} (D i)]
    {S : StageSystem C} {R : StageSystem D} (F : S.Morphism R)
    {i j : I} (h : i ≤ j) (K : C i) :
    (R.ι j).map ((F.β h).hom.app K) ≫
      F.functor.map ((S.transIso h).hom.app K) =
        (R.transIso h).hom.app ((F.Φ i).obj K) := by
  change (R.ι j).map ((F.β h).hom.app K) ≫
    F.functor.map (PairCategory.mkHom
      (X := ⟨j, (S.T h).obj K⟩) (Y := ⟨i, K⟩)
      j le_rfl h ((S.assoc h le_rfl).hom.app K)) =
      PairCategory.mkHom
        (X := ⟨j, (R.T h).obj ((F.Φ i).obj K)⟩)
        (Y := ⟨i, (F.Φ i).obj K⟩)
        j le_rfl h ((R.assoc h le_rfl).hom.app ((F.Φ i).obj K))
  erw [F.functor_map_mkHom, ι_map_eq le_rfl, PairCategory.mkHom_comp_mkHom]
  apply congrArg (PairCategory.mkHom j le_rfl h)
  dsimp only [Morphism.mapAt]
  have hc := congrArg (fun f ↦ f ≫ (F.β h).inv.app K) (F.coh h le_rfl K)
  simp only [Category.assoc, Iso.hom_inv_id_app] at hc
  erw [Category.comp_id] at hc
  exact hc

private theorem transport_transition_square
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type a} [∀ i, Category.{b} (C i)]
    {S T : StageSystem C} (e : S = T) (G : T.opposite.Morphism T)
    (he : ∀ i, (transportContravariantMorphism e G).Φ i = G.Φ i)
    {i j : I} (h : i ≤ j) (K : C i) :
    let F := transportContravariantMorphism e G
    let V := S.pairUnopFunctor ⋙ F.functor
    let r := fun i ↦ eqToIso (congrArg (fun d ↦ d ⋙ S.ι i) (he i).symm) ≪≫
      contravariantComparison S F i
    let t := eqToIso (congrArg (fun d ↦ d ⋙ S.ι j)
      (congrArg (fun U : StageSystem C ↦ U.T h) e).symm) ≪≫ S.transIso h
    (S.ι j).map ((G.β h).hom.app (op K)) ≫
      (r j).hom.app (op ((T.T h).obj K)) ≫ V.map (t.inv.app K).op =
        t.hom.app ((G.Φ i).obj (op K)) ≫ (r i).hom.app (op K) := by
  subst T
  dsimp only [transportContravariantMorphism] at he ⊢
  have heq : he = fun i ↦ (rfl : G.Φ i = G.Φ i) := Subsingleton.elim _ _
  rw [heq]
  erw [eqToIso_refl, eqToIso_refl, eqToIso_refl]
  simp only [Iso.refl_trans]
  change (S.ι j).map ((G.β h).hom.app (op K)) ≫ 𝟙 _ ≫
    (S.pairUnopFunctor ⋙ G.functor).map ((S.transIso h).inv.app K).op =
      (S.transIso h).hom.app ((G.Φ i).obj (op K)) ≫ 𝟙 _
  erw [Category.id_comp, Category.comp_id]
  change (S.ι j).map ((G.β h).hom.app (op K)) ≫
    G.functor.map ((S.opposite.transIso h).hom.app (op K)) = _
  exact transition_square G h (op K)

end CategoryTheory.StageSystem

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

/-- The finite inclusion-transition square for the descended dual.
Source: thm-coef-qbar-verdier, tower-coherence paragraph.
(blueprint: lem-coef-qbar-verdier-comparison-component)

Proof: expand the quotient representative map and apply the beta tower equation,
with the identity-component comparison cancelling on both sides. -/
theorem descended_comparison_formula (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
      (inclusion L).map ((F.beta E L h).hom.app (op K)) ≫
        (descendedComparison D l hl Ω X F hF L).hom.app
          (op ((transition l Ω X E L h).obj K)) ≫
        (descendedDual D l hl Ω X F hF).map
          ((inclusionTransition l Ω X E L h).inv.app K).op =
      (inclusionTransition l Ω X E L h).hom.app ((F.datum E).dual.obj (op K)) ≫
        (descendedComparison D l hl Ω X F hF E).hom.app (op K) := by
  intro E L h K
  exact StageSystem.transport_transition_square
    (stageSystem_eq_literalSystem l Ω X)
    (StageSystem.contravariantMorphism (literalSystem l Ω X)
      (fun E ↦ (F.datum E).dual) (fun {_ _} h ↦ F.beta _ _ h)
      (fun {_ _ _} h k K ↦ eq_of_heq (hF.2 _ _ _ h k K)))
    (finiteMorphism_phi D l hl Ω X F hF) h K

end WeilConjectures.CoefQbarVerdier
