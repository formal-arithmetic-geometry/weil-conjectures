/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Functor and transformation descent for unnormalized stage pairs

Source: blueprint filtered two-colimit model proof, “The comparison functor”, retained
order-1462 common-stage composition clause; StageSystem/Functor.lean, lines 56–395
(blueprint: lem-pur-unnormalized-pair-functor-descent).

The existing `StageSystem.Morphism` and its `Hom` encode precisely the tower and
transformation squares. Their descent constructions are reused without any unit constraint.
The auxiliary system `R` permits both pre- and post-whiskering, in independent universes.
-/

@[expose] public section
set_option autoImplicit false

universe w u v u' v' u'' v''

namespace CategoryTheory.StageSystem

open PairCategory

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {C : I → Type u} [∀ i : I, Category.{v} (C i)]
  {D : I → Type u'} [∀ i : I, Category.{v'} (D i)]
  {E : I → Type u''} [∀ i : I, Category.{v''} (E i)]

-- Retain the original nonempty-index hypothesis in the theorem interface.
set_option linter.unusedSectionVars false in
/-- All descent formulas for coherent families on unnormalized directed stage systems.
Source: blueprint filtered two-colimit model proof, “The comparison functor”, retained
order-1462 common-stage composition clause; StageSystem/Functor.lean, lines 56–395
(blueprint: lem-pur-unnormalized-pair-functor-descent).

Proof: (1) Apply lem-pur-associative-stage-family-descent: its tower and transformation
squares are the equations in `Morphism.coh` and `Morphism.Hom.comm`, with sides interchanged.
It supplies the functor and representative formulas, inclusion comparisons with identity
components, transformation descent, invertibility, identities, vertical composition and
composite-family comparisons. Naturality of the identity comparisons gives equality on arrows.
(2) For transport from m to n, apply the tower equation at both endpoints. Solve it for
b_in and b_jn, substitute in the conjugation formula at n, and cancel the source associators.
Naturality of b_mn at u cancels the middle comparisons. The result is precisely the target
transport of the conjugation formula at m. No extra associator cocycle or unit is used here.
(3) Post-whiskering by K has stage components K_i(eta_i). Compatibility follows by applying
K_j to the compatibility square for eta and then using naturality of K's comparison.
Its descended component is j_i(K_i(eta_i)), which equals K-bar(j_i(eta_i)) by the stage-arrow
formula. (4) Pre-whiskering by H has components eta_i(H_i(-)). Naturality of eta_j at H's
comparison, followed by compatibility of eta at H_i(x), is its compatibility square.
Its descended component is eta-bar at H-bar(i,x), by the literal object formula.
(5) Equality of compatible families is componentwise. Applying j_i preserves it; natural
transformation extensionality proves equality after descent. The identity, composition and
both whiskering formulas therefore preserve equations involving composite families as well. -/
theorem unnormalizedPairFunctorDescent
    (S : StageSystem C) (T : StageSystem D) (R : StageSystem E) (F : S.Morphism T) :
    (∀ X : S.PairCategory,
      F.functor.obj X = ⟨X.stage, (F.Φ X.stage).obj X.obj⟩) ∧
    (∀ {X Y : S.PairCategory} (m : I) (hX : X.stage ≤ m) (hY : Y.stage ≤ m)
      (f : X.toStage hX ⟶ Y.toStage hY),
      F.functor.map (mkHom m hX hY f) =
        mkHom (X := F.functor.obj X) (Y := F.functor.obj Y) m hX hY
          ((F.β hX).hom.app X.obj ≫ (F.Φ m).map f ≫ (F.β hY).inv.app Y.obj)) ∧
    (∀ {i j m n : I} (hi : i ≤ m) (hj : j ≤ m) (h : m ≤ n)
      (x : C i) (y : C j) (f : (S.T hi).obj x ⟶ (S.T hj).obj y),
      T.tr h (F.mapAt f) = F.mapAt (S.tr h f)) ∧
    (∀ (i : I) (x : C i),
      F.functor.obj ((S.ι i).obj x) = (T.ι i).obj ((F.Φ i).obj x)) ∧
    (∀ (i : I) (x y : C i) (f : x ⟶ y),
      F.functor.map ((S.ι i).map f) = (T.ι i).map ((F.Φ i).map f)) ∧
    (∀ (i : I) (x : C i), (F.ιCompFunctorIso i).hom.app x = 𝟙 _) ∧
    (∀ (G : S.Morphism T) (η : Morphism.Hom F G),
      (∀ X : S.PairCategory,
        (Morphism.descNatTrans η).app X = (T.ι X.stage).map ((η.τ X.stage).app X.obj)) ∧
      ((∀ i : I, IsIso (η.τ i)) → IsIso (Morphism.descNatTrans η)) ∧
      (∀ K : T.Morphism R, ∃ ω : Morphism.Hom (F.comp K) (G.comp K),
        (∀ i : I, ω.τ i = Functor.whiskerRight (η.τ i) (K.Φ i)) ∧
        (∀ X : S.PairCategory, (Morphism.descNatTrans ω).app X =
          K.functor.map ((Morphism.descNatTrans η).app X))) ∧
      (∀ H : R.Morphism S, ∃ ω : Morphism.Hom (H.comp F) (H.comp G),
        (∀ i : I, ω.τ i = Functor.whiskerLeft (H.Φ i) (η.τ i)) ∧
        (∀ X : R.PairCategory, (Morphism.descNatTrans ω).app X =
          (Morphism.descNatTrans η).app (H.functor.obj X))) ∧
      (∀ θ : Morphism.Hom F G, (∀ i : I, η.τ i = θ.τ i) →
        Morphism.descNatTrans η = Morphism.descNatTrans θ)) ∧
    (∀ X : S.PairCategory, (Morphism.id S).functor.obj X = X) ∧
    (∀ {X Y : S.PairCategory} (f : X ⟶ Y), (Morphism.id S).functor.map f = f) ∧
    (∀ (K : T.Morphism R) (X : S.PairCategory),
      (F.comp K).functor.obj X = K.functor.obj (F.functor.obj X)) ∧
    (∀ (K : T.Morphism R) {X Y : S.PairCategory} (f : X ⟶ Y),
      (F.comp K).functor.map f = K.functor.map (F.functor.map f)) ∧
    Morphism.descNatTrans (Morphism.Hom.id F) = 𝟙 F.functor ∧
    (∀ (G H : S.Morphism T) (η : Morphism.Hom F G) (θ : Morphism.Hom G H),
      Morphism.descNatTrans (η.comp θ) =
        Morphism.descNatTrans η ≫ Morphism.descNatTrans θ) := by
  refine ⟨F.functor_obj, ?_, ?_, ?_, ?_, F.ιCompFunctorIso_hom_app, ?_, ?_, ?_,
    ?_, ?_, Morphism.descNatTrans_id F, ?_⟩
  · intro X Y m hX hY f
    exact F.functor_map_mkHom hX hY f
  · intro i j m n hi hj h x y f
    exact F.tr_mapAt h f
  · intro i x
    rfl
  · intro i x y f
    exact F.functor_map_ι f
  · intro G η
    refine ⟨Morphism.descNatTrans_app η, Morphism.isIso_descNatTrans η, ?_, ?_, ?_⟩
    · intro K
      let ω : Morphism.Hom (F.comp K) (G.comp K) :=
        { τ := fun i ↦ Functor.whiskerRight (η.τ i) (K.Φ i)
          comm := by
            intro i j h x
            simp only [Functor.whiskerRight_app, Morphism.comp_β_hom_app]
            have hn := (K.β h).hom.naturality ((η.τ i).app x)
            simp only [Functor.comp_map] at hn
            rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
              η.comm, Functor.map_comp, Category.assoc] }
      refine ⟨ω, fun _ ↦ rfl, ?_⟩
      intro X
      exact (K.functor_map_ι ((η.τ X.stage).app X.obj)).symm
    · intro H
      let ω : Morphism.Hom (H.comp F) (H.comp G) :=
        { τ := fun i ↦ Functor.whiskerLeft (H.Φ i) (η.τ i)
          comm := by
            intro i j h x
            simp only [Functor.whiskerLeft_app, Morphism.comp_β_hom_app]
            rw [← Category.assoc, η.comm, Category.assoc, ← (η.τ j).naturality]
            simp only [Category.assoc, Functor.comp_obj] }
      exact ⟨ω, fun _ ↦ rfl, fun _ ↦ rfl⟩
    · intro θ h
      apply NatTrans.ext
      funext X
      exact congrArg (fun τ ↦ (T.ι X.stage).map (τ.app X.obj)) (h X.stage)
  · intro X
    cases X
    rfl
  · intro X Y f
    exact Morphism.functor_id_map f
  · intro K X
    rfl
  · intro K X Y f
    exact Morphism.functor_comp_map F K f
  · intro G H η θ
    exact Morphism.descNatTrans_comp η θ

end CategoryTheory.StageSystem
