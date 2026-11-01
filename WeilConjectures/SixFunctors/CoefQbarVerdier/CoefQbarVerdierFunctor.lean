/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemOpposite

/-! # The representative construction of the common-stage Verdier functor

Source: thm-coef-qbar-verdier, finite-stage descent, steps 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe w a b u v
open CategoryTheory Opposite

namespace CategoryTheory.StageSystem

def contravariantMorphism
    {I : Type w} [Preorder I] {C : I → Type a} [∀ i, Category.{b} (C i)]
    (S : StageSystem C) (d : ∀ i, (C i)ᵒᵖ ⥤ C i)
    (β : ∀ {i j}, (h : i ≤ j) → d i ⋙ S.T h ≅ (S.T h).op ⋙ d j)
    (hc : ∀ {i j k} (h : i ≤ j) (k' : j ≤ k) (K : C i),
      (S.T k').map ((β h).hom.app (op K)) ≫
        (β k').hom.app (op ((S.T h).obj K)) =
      (S.assoc h k').hom.app ((d i).obj (op K)) ≫
        (β (h.trans k')).hom.app (op K) ≫
        (d k).map ((S.assoc h k').hom.app K).op) : S.opposite.Morphism S where
  Φ := d
  β := β
  coh h k K := by
    dsimp only [StageSystem.opposite, NatIso.op, NatTrans.op, Iso.symm]
    simp only [Functor.op_obj]
    have hc' := hc h k K.unop
    simp only [op_unop] at hc'
    rw [← Category.assoc, hc']
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id]
    erw [Functor.map_id, Category.comp_id]

def transportContravariantMorphism
    {I : Type w} [Preorder I] {C : I → Type a} [∀ i, Category.{b} (C i)]
    {S T : StageSystem C} (h : S = T) (F : T.opposite.Morphism T) :
    S.opposite.Morphism S := h.symm ▸ F

private theorem transportContravariantMorphism_phi
    {I : Type w} [Preorder I] {C : I → Type a} [∀ i, Category.{b} (C i)]
    {S T : StageSystem C} (h : S = T) (F : T.opposite.Morphism T) (i : I) :
    (transportContravariantMorphism h F).Φ i = F.Φ i := by
  subst T
  rfl

/-- Opposite representatives identify the two literal stage inclusions. -/
def contravariantComparison
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type a} [∀ i, Category.{b} (C i)]
    (S : StageSystem C) (F : S.opposite.Morphism S) (i : I) :
    F.Φ i ⋙ S.ι i ≅ (S.ι i).op ⋙ (S.pairUnopFunctor ⋙ F.functor) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    dsimp only [Functor.comp_map, Iso.refl_hom]
    erw [Category.comp_id, Category.id_comp]
    change (S.ι i).map ((F.Φ i).map f) =
      F.functor.map ((S.opposite.ι i).map f)
    exact (F.functor_map_ι f).symm)

theorem contravariantComparison_hom
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type a} [∀ i, Category.{b} (C i)]
    (S : StageSystem C) (F : S.opposite.Morphism S) (i : I) (K : (C i)ᵒᵖ) :
    HEq ((contravariantComparison S F i).hom.app K)
      (𝟙 ((S.ι i).obj ((F.Φ i).obj K))) := HEq.rfl

theorem contravariantComparison_transport_hom
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type a} [∀ i, Category.{b} (C i)]
    (S : StageSystem C) (F : S.opposite.Morphism S) (i : I)
    (d : (C i)ᵒᵖ ⥤ C i) (h : d = F.Φ i) (K : (C i)ᵒᵖ) :
    HEq (((eqToIso (congrArg (fun e ↦ e ⋙ S.ι i) h) ≪≫
      contravariantComparison S F i).hom.app K)) (𝟙 ((S.ι i).obj (d.obj K))) := by
  subst d
  simpa only [eqToIso_refl, Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] using contravariantComparison_hom S F i K

end CategoryTheory.StageSystem

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.StageSystem

namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition associator)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Use the literal transition functors and associators before transporting to the
published stage system. The cocycle is the prescribed tensor associator cocycle. -/
def literalSystem : StageSystem (Stage l Ω X) where
  T := fun {E L} h ↦ transition l Ω X E L h
  assoc := fun {E L M} h k ↦ associator l Ω X E L M h k
  cocycle := fun {_ _ _ _} h k m K ↦
    GeneralAlgebraicallyClosedCoefficients.associator_cocycle l Ω X _ _ _ _ h k m K

/-- Both stage systems have exactly the prescribed data fields. -/
theorem stageSystem_eq_literalSystem :
    GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X = literalSystem l Ω X := by
  apply (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω X).unique
  · exact (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω X).exists
      |>.choose_spec
  · exact ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩

/-- Tower coherence is exactly the axiom for a morphism out of the opposite stages. -/
def finiteMorphism (F : Finite D l hl Ω X) (hF : FiniteCoherent D l hl Ω X F) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).opposite.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X) :=
  transportContravariantMorphism (stageSystem_eq_literalSystem l Ω X)
    (contravariantMorphism (literalSystem l Ω X) (fun E ↦ (F.datum E).dual)
      (fun {_ _} h ↦ F.beta _ _ h) (fun {_ _ _} h k K ↦
        eq_of_heq (hF.2 _ _ _ h k K)))

/-- Equality transport does not change the finite functors. -/
theorem finiteMorphism_phi (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) (E : Index l Ω) :
    (finiteMorphism D l hl Ω X F hF).Φ E = (F.datum E).dual :=
  transportContravariantMorphism_phi _ _ E

/-- Reverse representatives and apply the coherent finite duality maps.
The object retains its original coefficient field; every arrow is an actual quotient map. -/
def descendedDual (F : Finite D l hl Ω X) (hF : FiniteCoherent D l hl Ω X F) :
    (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).pairUnopFunctor ⋙
    (finiteMorphism D l hl Ω X F hF).functor

/-- The descended dual retains the literal stage of every object. -/
theorem descendedDual_obj (F : Finite D l hl Ω X) (hF : FiniteCoherent D l hl Ω X F)
    (E : Index l Ω) (K : Stage l Ω X E) :
    (descendedDual D l hl Ω X F hF).obj (op ((inclusion E).obj K)) =
      (inclusion E).obj ((F.datum E).dual.obj (op K)) := by
  change (inclusion E).obj (((finiteMorphism D l hl Ω X F hF).Φ E).obj (op K)) = _
  rw [finiteMorphism_phi]
  rfl

/-- The finite comparison has the identity representative as its component. -/
def descendedComparison (F : Finite D l hl Ω X) (hF : FiniteCoherent D l hl Ω X F)
    (E : Index l Ω) :
    (F.datum E).dual ⋙ inclusion E ≅ (inclusion E).op ⋙ descendedDual D l hl Ω X F hF :=
  eqToIso (congrArg (fun d ↦ d ⋙ inclusion E)
    (finiteMorphism_phi D l hl Ω X F hF E).symm) ≪≫
      contravariantComparison _ (finiteMorphism D l hl Ω X F hF) E

/-- Equality transport in the comparison contributes only an identity component. -/
theorem descendedComparison_hom (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) (E : Index l Ω) (K : Stage l Ω X E) :
    HEq ((descendedComparison D l hl Ω X F hF E).hom.app (op K))
      (𝟙 ((inclusion E).obj ((F.datum E).dual.obj (op K)))) := by
  apply contravariantComparison_transport_hom _ (finiteMorphism D l hl Ω X F hF) E
    (F.datum E).dual (finiteMorphism_phi D l hl Ω X F hF E).symm (op K)

end WeilConjectures.CoefQbarVerdier
