/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFunctor

/-! # Finite biduality component for the common-stage dual

Source: thm-coef-qbar-verdier, biduality portion of proof step 4.
(blueprint: lem-coef-qbar-verdier-biduality-component)

The finite biduality maps are transported through the fixed inclusion comparisons.
The remaining proof is the naturality and inverse calculation on representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w a b
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace CategoryTheory.StageSystem

private theorem double_mapAt
    {I : Type w} [Preorder I] {C : I → Type a} [∀ i, Category.{b} (C i)]
    (S : StageSystem C) (F : S.opposite.Morphism S)
    (δ : ∀ i, 𝟭 (C i) ≅ (F.Φ i).rightOp ⋙ F.Φ i)
    (hδ : ∀ {i j} (h : i ≤ j) (K : C i),
      (S.T h).map ((δ i).hom.app K) ≫
        (F.β h).hom.app (op ((F.Φ i).obj (op K))) =
      (δ j).hom.app ((S.T h).obj K) ≫
        (F.Φ j).map ((F.β h).hom.app (op K)).op)
    {i j n : I} (hi : i ≤ n) (hj : j ≤ n) (K : C i) (M : C j)
    (f : (S.T hi).obj K ⟶ (S.T hj).obj M) :
    (S.T hi).map ((δ i).hom.app K) ≫
      F.mapAt (hi := hi) (hj := hj)
        (x := op ((F.Φ i).obj (op K))) (y := op ((F.Φ j).obj (op M)))
        (F.mapAt (hi := hj) (hj := hi) (x := op M) (y := op K) f.op).op =
      f ≫ (S.T hj).map ((δ j).hom.app M) := by
  have hleft : (S.T hi).map ((δ i).hom.app K) ≫
      (F.β hi).hom.app (op ((F.Φ i).obj (op K))) ≫
      (F.Φ n).map ((F.β hi).inv.app (op K)).op =
        (δ n).hom.app ((S.T hi).obj K) := by
    erw [← Category.assoc, hδ, Category.assoc, ← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id_app, op_id, Functor.map_id, Category.comp_id]
  have hright : (δ n).hom.app ((S.T hj).obj M) ≫
      (F.Φ n).map ((F.β hj).hom.app (op M)).op ≫
      (F.β hj).inv.app (op ((F.Φ j).obj (op M))) =
        (S.T hj).map ((δ j).hom.app M) := by
    erw [← Category.assoc, ← hδ, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  calc
    _ = ((S.T hi).map ((δ i).hom.app K) ≫
        (F.β hi).hom.app (op ((F.Φ i).obj (op K))) ≫
        (F.Φ n).map ((F.β hi).inv.app (op K)).op) ≫
        (F.Φ n).map ((F.Φ n).map f.op).op ≫
        (F.Φ n).map ((F.β hj).hom.app (op M)).op ≫
        (F.β hj).inv.app (op ((F.Φ j).obj (op M))) := by
      dsimp only [Morphism.mapAt]
      simp only [op_comp]
      erw [Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      rfl
    _ = (δ n).hom.app ((S.T hi).obj K) ≫
        (F.Φ n).map ((F.Φ n).map f.op).op ≫
        (F.Φ n).map ((F.β hj).hom.app (op M)).op ≫
        (F.β hj).inv.app (op ((F.Φ j).obj (op M))) := by erw [hleft]; rfl
    _ = f ≫ ((δ n).hom.app ((S.T hj).obj M) ≫
        (F.Φ n).map ((F.β hj).hom.app (op M)).op ≫
        (F.β hj).inv.app (op ((F.Φ j).obj (op M)))) := by
      have hn := (δ n).hom.naturality f
      change f ≫ (δ n).hom.app _ = (δ n).hom.app _ ≫
        (F.Φ n).map ((F.Φ n).map f.op).op at hn
      rw [← Category.assoc, ← Category.assoc, ← hn]
    _ = _ := by erw [hright]

private theorem pair_biduality
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type a} [∀ i, Category.{b} (C i)]
    (S : StageSystem C) (F : S.opposite.Morphism S)
    (δ : ∀ i, 𝟭 (C i) ≅ (F.Φ i).rightOp ⋙ F.Φ i)
    (hδ : ∀ {i j} (h : i ≤ j) (K : C i),
      (S.T h).map ((δ i).hom.app K) ≫
        (F.β h).hom.app (op ((F.Φ i).obj (op K))) =
      (δ j).hom.app ((S.T h).obj K) ≫
        (F.Φ j).map ((F.β h).hom.app (op K)).op) :
    let V := S.pairUnopFunctor ⋙ F.functor
    ∃ ε : 𝟭 S.PairCategory ≅ V.rightOp ⋙ V,
      ∀ i, WeilConjectures.SfClassEvaluationCompatible (S.ι i) (F.Φ i) V
        (δ i).hom ε.hom (contravariantComparison S F i) := by
  let V := S.pairUnopFunctor ⋙ F.functor
  let ε : 𝟭 S.PairCategory ≅ V.rightOp ⋙ V := NatIso.ofComponents
    (fun K ↦ (S.ι K.stage).mapIso ((δ K.stage).app K.obj)) (by
      intro K M f
      induction f using PairCategory.hom_induction with
      | h n hK hM f =>
        change PairCategory.mkHom n hK hM f ≫
          (S.ι M.stage).map ((δ M.stage).hom.app M.obj) =
          (S.ι K.stage).map ((δ K.stage).hom.app K.obj) ≫
            V.map (V.map (PairCategory.mkHom n hK hM f).op).op
        rw [ι_map_eq hK, ι_map_eq hM]
        change PairCategory.mkHom (X := K) (Y := M) n hK hM f ≫
          PairCategory.mkHom (X := M) (Y := V.obj (op (V.obj (op M)))) n hM hM
            ((S.T hM).map ((δ M.stage).hom.app M.obj)) =
          PairCategory.mkHom (X := K) (Y := V.obj (op (V.obj (op K)))) n hK hK
            ((S.T hK).map ((δ K.stage).hom.app K.obj)) ≫
          PairCategory.mkHom (X := V.obj (op (V.obj (op K))))
            (Y := V.obj (op (V.obj (op M)))) n hK hM _
        erw [PairCategory.mkHom_comp_mkHom, PairCategory.mkHom_comp_mkHom]
        exact congrArg (PairCategory.mkHom
          (X := K) (Y := V.obj (op (V.obj (op M)))) n hK hM)
          (double_mapAt S F δ hδ hK hM K.obj M.obj f).symm)
  refine ⟨ε, ?_⟩
  intro i K
  change (S.ι i).map ((δ i).hom.app K) ≫ 𝟙 _ ≫
      V.map (𝟙 (op ((S.ι i).obj ((F.Φ i).obj (op K))))) =
    (S.ι i).map ((δ i).hom.app K)
  erw [V.map_id, Category.id_comp, Category.comp_id]

private theorem transported_biduality
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type a} [∀ i, Category.{b} (C i)]
    {S T : StageSystem C} (e : S = T) (G : T.opposite.Morphism T)
    (he : ∀ i, (transportContravariantMorphism e G).Φ i = G.Φ i)
    (δ : ∀ i, 𝟭 (C i) ≅ (G.Φ i).rightOp ⋙ G.Φ i)
    (hδ : ∀ {i j} (h : i ≤ j) (K : C i),
      (T.T h).map ((δ i).hom.app K) ≫
        (G.β h).hom.app (op ((G.Φ i).obj (op K))) =
      (δ j).hom.app ((T.T h).obj K) ≫
        (G.Φ j).map ((G.β h).hom.app (op K)).op) :
    let F := transportContravariantMorphism e G
    let V := S.pairUnopFunctor ⋙ F.functor
    let r := fun i ↦ eqToIso (congrArg (fun d ↦ d ⋙ S.ι i) (he i).symm) ≪≫
      contravariantComparison S F i
    ∃ ε : 𝟭 S.PairCategory ≅ V.rightOp ⋙ V,
      ∀ i, WeilConjectures.SfClassEvaluationCompatible (S.ι i) (G.Φ i) V
        (δ i).hom ε.hom (r i) := by
  subst T
  dsimp only [transportContravariantMorphism] at he ⊢
  obtain ⟨ε, hε⟩ := pair_biduality S G δ hδ
  refine ⟨ε, ?_⟩
  intro i
  erw [eqToIso_refl]
  simpa only [Iso.refl_trans] using hε i

end CategoryTheory.StageSystem

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

/-- The finite biduality components descend and satisfy the prescribed evaluation
compatibility.  This is strictly the biduality part of the parent conjunction.
Source: thm-coef-qbar-verdier, biduality portion of proof step 4.
(blueprint: lem-coef-qbar-verdier-biduality-component)

Proof: include the finite biduality map, transport it twice through the canonical
comparisons, and check naturality and the two inverse composites at a common finite
stage. -/
theorem descended_biduality (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    ∃ δ : 𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω X) ≅
        (descendedDual D l hl Ω X F hF).rightOp ⋙ descendedDual D l hl Ω X F hF,
      ∀ E : Index l Ω,
        SfClassEvaluationCompatible (inclusion (Y := X) E) (F.datum E).dual
          (descendedDual D l hl Ω X F hF) (F.datum E).bidual.hom δ.hom
          (descendedComparison D l hl Ω X F hF E) := by
  apply StageSystem.transported_biduality
    (stageSystem_eq_literalSystem l Ω X)
    (StageSystem.contravariantMorphism (literalSystem l Ω X)
      (fun E ↦ (F.datum E).dual) (fun {_ _} h ↦ F.beta _ _ h)
      (fun {_ _ _} h k K ↦ eq_of_heq (hF.2 _ _ _ h k K)))
    (finiteMorphism_phi D l hl Ω X F hF) (fun E ↦ (F.datum E).bidual)
  intro E L h K
  have hb := eq_of_heq (F.betaNormalized E L h)
  change (transition l Ω X E L h).map ((F.datum E).bidual.hom.app K) ≫
      (F.beta E L h).hom.app (op ((F.datum E).dual.obj (op K))) =
    (F.datum L).bidual.hom.app ((transition l Ω X E L h).obj K) ≫
      (F.datum L).dual.map ((F.beta E L h).hom.app (op K)).op
  rw [hb]
  exact (F.normalized E L h).2.2.2 K

end WeilConjectures.CoefQbarVerdier
