/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralTensorShiftProperties
public import WeilConjectures.SixFunctors.IntegralExpressionOccurrences

/-! # Shifts of independent expression inputs

Source: blueprint purity transport, Step 2, and the independent input convention
(blueprint: lem-pur-independent-expression-shift-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
attribute [local irreducible] HasDerivedCategory.standard


/-- Shift comparisons for each primitive operation; tensor slots remain separate.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
structure InterpretationShifts {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    [∀ W, HasShift (C W) ℤ] (d : Interpretation C) where
  pull {U V : Scheme.{u}} (f : U ⟶ V) : (d.pull f).CommShift ℤ
  push {U V : Scheme.{u}} (f : U ⟶ V) : (d.push f).CommShift ℤ
  shriek {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] : (d.shriek j).CommShift ℤ
  compactSupport {U V : Scheme.{u}} (f : U ⟶ V) (c : Compactification f) :
    (d.compactSupport f c).CommShift ℤ
  tensorLeft (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (C W) r ⋙ d.tensor W ≅ d.tensor W ⋙ shiftFunctor (C W) r
  tensorRight (W : Scheme.{u}) (r : ℤ) :
    completedTensorShiftSecond (C W) r ⋙ d.tensor W ≅
      d.tensor W ⋙ shiftFunctor (C W) r

/-- Reindex shifts through the actual single-slot context, with the designated
left or right tensor comparison at every tensor vertex.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def Expression.SlotContext.shift {B : Scheme.{u}} {C : Scheme.{u} → Type v}
    [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ] {d : Interpretation C}
    (a : InterpretationShifts d) {A : Over B} (r : ℤ) :
    {W : Over B} → (e : Expression.SlotContext d A W) → (P : C A.left) →
      e.evaluate.obj (P⟦r⟧) ≅ (e.evaluate.obj P)⟦r⟧
  | _, .input, _ => Iso.refl _
  | _, .pull f e, P => (d.pull f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.pull f.left) (self := a.pull f.left) r).app (e.evaluate.obj P)
  | _, .push f _ e, P => (d.push f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.push f.left) (self := a.push f.left) r).app (e.evaluate.obj P)
  | _, .shriek j hj _ e, P =>
    letI := hj
    (d.shriek j.left).mapIso (e.shift a r P) ≪≫
      (Functor.commShiftIso (d.shriek j.left) (self := a.shriek j.left) r).app
        (e.evaluate.obj P)
  | _, .compactSupport f c e, P => (d.compactSupport f.left c).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.compactSupport f.left c)
      (self := a.compactSupport f.left c) r).app (e.evaluate.obj P)
  | W, .tensorLeft e N, P =>
    ((Functor.curry.obj (d.tensor W.left)).flip.obj N).mapIso (e.shift a r P) ≪≫
      (a.tensorLeft W.left r).app (e.evaluate.obj P, N)
  | W, .tensorRight M e, P =>
    ((Functor.curry.obj (d.tensor W.left)).obj M).mapIso (e.shift a r P) ≪≫
      (a.tensorRight W.left r).app (M, e.evaluate.obj P)

open Classical in
/-- The actual comparison for a single independently labelled input.
Its endpoint identifications are equalities of explicit evaluations, not chosen isos.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.shift {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    (d : Interpretation C) (a : InterpretationShifts d) {W : Over B}
    (e : IndependentExpression B I X W) (K : ∀ i, C (X i).left) (i : I) (r : ℤ) :
    (e.val.evaluate d).obj (Function.update K i ((K i)⟦r⟧)) ≅
      ((e.val.evaluate d).obj K)⟦r⟧ :=
  (eqToIso (e.variableContext_evaluate d K i ((K i)⟦r⟧)).1).symm ≪≫
    (e.variableContext d K i).shift a r (K i) ≪≫
    (shiftFunctor (C W.left) r).mapIso
      (eqToIso (e.variableContext_evaluate d K i (K i)).2)

private theorem assemble_heq {D : Type*} {E : Type*} [Category* D] [Category* E]
    [HasShift E ℤ] (F : D ⥤ E) (T : D ⥤ D) (r : ℤ)
    (σ : T ⋙ F ≅ F ⋙ shiftFunctor E r)
    {U U' P P' : D} (hU : U = U') (hP : P = P')
    {f : U ⟶ T.obj P} {g : U' ⟶ T.obj P'} (h : HEq f g) :
    HEq (F.map f ≫ σ.hom.app P) (F.map g ≫ σ.hom.app P') := by
  subst U'
  subst P'
  cases h
  rfl

private theorem pair_hom_heq {D : Type*} {E : Type*} [Category* D] [Category* E]
    {P Q P' Q' : D} {R S R' S' : E}
    (hP : P = P') (hQ : Q = Q') (hR : R = R') (hS : S = S')
    {f : P ⟶ Q} {f' : P' ⟶ Q'} {g : R ⟶ S} {g' : R' ⟶ S'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f, g) (f', g') := by
  subst P'
  subst Q'
  subst R'
  subst S'
  cases hf
  cases hg
  rfl

private def pairIso {D : Type*} {E : Type*} {F : Type*}
    [Category* D] [Category* E] [Category* F]
    {P Q : D ⥤ E} {R S : D ⥤ F} (α : P ≅ Q) (β : R ≅ S) :
    P.prod' R ≅ Q.prod' S where
  hom := NatTrans.prod' α.hom β.hom
  inv := NatTrans.prod' α.inv β.inv
  hom_inv_id := by ext K <;> simp
  inv_hom_id := by ext K <;> simp

private theorem context_absent {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] (d : Interpretation C)
    (K : ∀ i, C (X i).left) (i : I) {W : Over B} (e : Expression B I X W)
    (h : ∀ j, e.occurrenceLabel j ≠ i) : e.variableContext d K i = none := by
  classical
  induction e with
  | var j =>
    have hij : i ≠ j := Ne.symm (h PUnit.unit)
    simp [Expression.variableContext, hij]
  | pull f e ih => simp [Expression.variableContext, ih h]
  | push f hp e ih => simp [Expression.variableContext, ih h]
  | shriek j hj hq e ih => simp [Expression.variableContext, ih h]
  | compactSupport f c e ih => simp [Expression.variableContext, ih h]
  | tensor e t ih jt =>
    simp [Expression.variableContext, ih (fun j ↦ h (Sum.inl j)),
      jt (fun j ↦ h (Sum.inr j))]

private theorem shift_absent {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    (d : Interpretation C) (i : I) (r : ℤ) {W : Over B} (e : Expression B I X W)
    (h : ∀ j, e.occurrenceLabel j ≠ i) :
    inputShift (fun j ↦ C (X j).left) i r ⋙ e.evaluate d = e.evaluate d := by
  classical
  induction e with
  | var j =>
    have hij : i ≠ j := Ne.symm (h PUnit.unit)
    change Pi.eval _ j ⋙ (if i = j then shiftFunctor _ r else 𝟭 _) = Pi.eval _ j
    rw [if_neg hij]
    rfl
  | pull f e ih =>
    change (inputShift _ i r ⋙ e.evaluate d) ⋙ d.pull f.left = _
    rw [ih h]
    rfl
  | push f hp e ih =>
    change (inputShift _ i r ⋙ e.evaluate d) ⋙ d.push f.left = _
    rw [ih h]
    rfl
  | shriek j hj hq e ih =>
    let := hj
    change (inputShift _ i r ⋙ e.evaluate d) ⋙ d.shriek j.left = _
    rw [ih h]
    rfl
  | compactSupport f c e ih =>
    change (inputShift _ i r ⋙ e.evaluate d) ⋙ d.compactSupport f.left c = _
    rw [ih h]
    rfl
  | tensor e t ih jt =>
    change ((inputShift _ i r ⋙ e.evaluate d).prod'
      (inputShift _ i r ⋙ t.evaluate d)) ⋙ d.tensor _ = _
    rw [ih (fun j ↦ h (Sum.inl j)), jt (fun j ↦ h (Sum.inr j))]
    rfl

-- Besides the natural isomorphism, retain its concrete context at every family.
-- The two object equalities allow heterogeneous comparison before endpoint transport.
private theorem shift_witness {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    (d : Interpretation C) (a : InterpretationShifts d) (i : I) (r : ℤ)
    {W : Over B} (e : Expression B I X W) (h : Function.Injective e.occurrenceLabel)
    (j : e.Occurrences) (hj : e.occurrenceLabel j = i) :
    ∃ α : inputShift (fun k ↦ C (X k).left) i r ⋙ e.evaluate d ≅
        e.evaluate d ⋙ shiftFunctor (C W.left) r,
      ∀ K : ∀ k, C (X k).left, ∃ c : Expression.SlotContext d (X i) W,
        e.variableContext d K i = some c ∧
        c.evaluate.obj (K i) = (e.evaluate d).obj K ∧
        c.evaluate.obj ((K i)⟦r⟧) = (e.evaluate d).obj ((inputShift _ i r).obj K) ∧
        HEq (α.hom.app K) (c.shift a r (K i)).hom := by
  classical
  induction e with
  | var k =>
    change k = i at hj
    subst i
    have hs : inputShift (fun j ↦ C (X j).left) k r ⋙ Pi.eval _ k =
        Pi.eval (fun j ↦ C (X j).left) k ⋙ shiftFunctor (C (X k).left) r := by
      change Pi.eval _ k ⋙ (if k = k then shiftFunctor _ r else 𝟭 _) = _
      rw [if_pos rfl]
    refine ⟨eqToIso hs, fun K ↦ ⟨.input, ?_, rfl, ?_, ?_⟩⟩
    · simp [Expression.variableContext]
    · simp [Expression.SlotContext.evaluate, Expression.evaluate, inputShift]
    · simp only [eqToIso.hom, eqToHom_app]
      exact eqToHom_heq_id_cod _ _ _
  | pull f e ih =>
    obtain ⟨α, hα⟩ := ih h j hj
    refine ⟨Functor.isoWhiskerRight α (d.pull f.left) ≪≫
      Functor.isoWhiskerLeft (e.evaluate d)
        (Functor.commShiftIso (d.pull f.left) (self := a.pull f.left) r), ?_⟩
    intro K
    obtain ⟨c, hc, h0, hs, hh⟩ := hα K
    refine ⟨.pull f c, ?_, congrArg (d.pull f.left).obj h0,
      congrArg (d.pull f.left).obj hs, ?_⟩
    · simp [Expression.variableContext, hc]
    · exact assemble_heq (d.pull f.left) (shiftFunctor _ r) r
        (Functor.commShiftIso (d.pull f.left) (self := a.pull f.left) r)
        hs.symm h0.symm hh
  | push f hp e ih =>
    obtain ⟨α, hα⟩ := ih h j hj
    refine ⟨Functor.isoWhiskerRight α (d.push f.left) ≪≫
      Functor.isoWhiskerLeft (e.evaluate d)
        (Functor.commShiftIso (d.push f.left) (self := a.push f.left) r), ?_⟩
    intro K
    obtain ⟨c, hc, h0, hs, hh⟩ := hα K
    refine ⟨.push f hp c, ?_, congrArg (d.push f.left).obj h0,
      congrArg (d.push f.left).obj hs, ?_⟩
    · simp [Expression.variableContext, hc]
    · exact assemble_heq (d.push f.left) (shiftFunctor _ r) r
        (Functor.commShiftIso (d.push f.left) (self := a.push f.left) r)
        hs.symm h0.symm hh
  | shriek f hf hq e ih =>
    let := hf
    obtain ⟨α, hα⟩ := ih h j hj
    refine ⟨Functor.isoWhiskerRight α (d.shriek f.left) ≪≫
      Functor.isoWhiskerLeft (e.evaluate d)
        (Functor.commShiftIso (d.shriek f.left) (self := a.shriek f.left) r), ?_⟩
    intro K
    obtain ⟨c, hc, h0, hs, hh⟩ := hα K
    refine ⟨.shriek f hf hq c, ?_, congrArg (d.shriek f.left).obj h0,
      congrArg (d.shriek f.left).obj hs, ?_⟩
    · simp [Expression.variableContext, hc]
    · exact assemble_heq (d.shriek f.left) (shiftFunctor _ r) r
        (Functor.commShiftIso (d.shriek f.left) (self := a.shriek f.left) r)
        hs.symm h0.symm hh
  | compactSupport f cf e ih =>
    obtain ⟨α, hα⟩ := ih h j hj
    refine ⟨Functor.isoWhiskerRight α (d.compactSupport f.left cf) ≪≫
      Functor.isoWhiskerLeft (e.evaluate d)
        (Functor.commShiftIso (d.compactSupport f.left cf)
          (self := a.compactSupport f.left cf) r), ?_⟩
    intro K
    obtain ⟨c, hc, h0, hs, hh⟩ := hα K
    refine ⟨.compactSupport f cf c, ?_, congrArg (d.compactSupport f.left cf).obj h0,
      congrArg (d.compactSupport f.left cf).obj hs, ?_⟩
    · simp [Expression.variableContext, hc]
    · exact assemble_heq (d.compactSupport f.left cf) (shiftFunctor _ r) r
        (Functor.commShiftIso (d.compactSupport f.left cf)
          (self := a.compactSupport f.left cf) r) hs.symm h0.symm hh
  | @tensor W e t ih jt =>
    have hl : Function.Injective e.occurrenceLabel :=
      fun a b hab ↦ Sum.inl.inj (h (a₁ := Sum.inl a) (a₂ := Sum.inl b) hab)
    have hr : Function.Injective t.occurrenceLabel :=
      fun a b hab ↦ Sum.inr.inj (h (a₁ := Sum.inr a) (a₂ := Sum.inr b) hab)
    cases j with
    | inl j =>
      have ha : ∀ k, t.occurrenceLabel k ≠ i := by
        intro k hk
        have bad := h (a₁ := Sum.inl j) (a₂ := Sum.inr k) (hj.trans hk.symm)
        cases bad
      obtain ⟨α, hα⟩ := ih hl j hj
      have ht := shift_absent d i r t ha
      let β := eqToIso ht
      refine ⟨Functor.isoWhiskerRight (pairIso α β) (d.tensor W.left) ≪≫
        Functor.isoWhiskerLeft ((e.evaluate d).prod' (t.evaluate d))
          (a.tensorLeft W.left r), ?_⟩
      intro K
      obtain ⟨c, hc, h0, hs, hh⟩ := hα K
      refine ⟨.tensorLeft c ((t.evaluate d).obj K), ?_, ?_, ?_, ?_⟩
      · simp [Expression.variableContext, hc]
      · exact congrArg (d.tensor W.left).obj (Prod.ext h0 rfl)
      · exact congrArg (d.tensor W.left).obj
          (Prod.ext hs (Functor.congr_obj ht K).symm)
      · change HEq ((d.tensor W.left).map
          (CategoryTheory.Prod.mkHom (α.hom.app K) (β.hom.app K)) ≫ _)
          ((d.tensor W.left).map (CategoryTheory.Prod.mkHom
            (c.shift a r (K i)).hom (𝟙 ((t.evaluate d).obj K))) ≫ _)
        apply assemble_heq (d.tensor W.left) (tensorShiftFirst _ r) r
          (a.tensorLeft W.left r)
          (U := ((e.evaluate d).obj ((inputShift _ i r).obj K),
            (t.evaluate d).obj ((inputShift _ i r).obj K)))
          (U' := (c.evaluate.obj ((K i)⟦r⟧), (t.evaluate d).obj K))
          (P := ((e.evaluate d).obj K, (t.evaluate d).obj K))
          (P' := (c.evaluate.obj (K i), (t.evaluate d).obj K))
          (Prod.ext hs.symm (Functor.congr_obj ht K)) (Prod.ext h0.symm rfl)
        have hb : HEq (β.hom.app K) (𝟙 ((t.evaluate d).obj K)) := by
          dsimp only [β, eqToIso.hom]
          rw [eqToHom_app]
          exact eqToHom_heq_id_cod _ _ _
        exact pair_hom_heq hs.symm (congrArg (shiftFunctor _ r).obj h0.symm)
          (Functor.congr_obj ht K) rfl hh hb
    | inr j =>
      have ha : ∀ k, e.occurrenceLabel k ≠ i := by
        intro k hk
        have bad := h (a₁ := Sum.inl k) (a₂ := Sum.inr j) (hk.trans hj.symm)
        cases bad
      obtain ⟨α, hα⟩ := jt hr j hj
      have he := shift_absent d i r e ha
      let β := eqToIso he
      refine ⟨Functor.isoWhiskerRight (pairIso β α) (d.tensor W.left) ≪≫
        Functor.isoWhiskerLeft ((e.evaluate d).prod' (t.evaluate d))
          (a.tensorRight W.left r), ?_⟩
      intro K
      obtain ⟨c, hc, h0, hs, hh⟩ := hα K
      refine ⟨.tensorRight ((e.evaluate d).obj K) c, ?_, ?_, ?_, ?_⟩
      · simp [Expression.variableContext, context_absent d K i e ha, hc]
      · exact congrArg (d.tensor W.left).obj (Prod.ext rfl h0)
      · exact congrArg (d.tensor W.left).obj
          (Prod.ext (Functor.congr_obj he K).symm hs)
      · change HEq ((d.tensor W.left).map
          (CategoryTheory.Prod.mkHom (β.hom.app K) (α.hom.app K)) ≫ _)
          ((d.tensor W.left).map (CategoryTheory.Prod.mkHom
            (𝟙 ((e.evaluate d).obj K)) (c.shift a r (K i)).hom) ≫ _)
        apply assemble_heq (d.tensor W.left) (completedTensorShiftSecond _ r) r
          (a.tensorRight W.left r)
          (U := ((e.evaluate d).obj ((inputShift _ i r).obj K),
            (t.evaluate d).obj ((inputShift _ i r).obj K)))
          (U' := ((e.evaluate d).obj K, c.evaluate.obj ((K i)⟦r⟧)))
          (P := ((e.evaluate d).obj K, (t.evaluate d).obj K))
          (P' := ((e.evaluate d).obj K, c.evaluate.obj (K i)))
          (Prod.ext (Functor.congr_obj he K) hs.symm) (Prod.ext rfl h0.symm)
        have hb : HEq (β.hom.app K) (𝟙 ((e.evaluate d).obj K)) := by
          dsimp only [β, eqToIso.hom]
          rw [eqToHom_app]
          exact eqToHom_heq_id_cod _ _ _
        exact pair_hom_heq (Functor.congr_obj he K) rfl hs.symm
          (congrArg (shiftFunctor _ r).obj h0.symm) hb hh

/-- The recursive shift comparison is natural in all independently labelled inputs.
Source: blueprint purity transport, Step 2, inherited shift equations
(blueprint: lem-pur-independent-expression-shift-naturality).

Proof: follow the unique occurrence labelled i. A variable gives the identity
comparison; each unary operation composes its functorial image with the natural
shift of that operation. At a tensor vertex, injectivity of the occurrence-label
map excludes i from the other subtree. Thus dependent update leaves that subtree
unchanged, including its map on any family morphism. Naturality of the left or
right tensor comparison in both operands gives the square at that vertex.
The endpoint equality transports are the evaluation identities for this same
context, so functoriality of equality transport gives the displayed square. -/
theorem IndependentExpression.shift_naturality_generic
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    (d : Interpretation C) (a : InterpretationShifts d) {W : Over B}
    (e : IndependentExpression B I X W) (K N : ∀ i, C (X i).left)
    (f : K ⟶ N) (i : I) (r : ℤ) :
    (e.val.evaluate d).map ((inputShift _ i r).map f) ≫
        ((e.val.evaluate d).mapIso (eqToIso (inputShift_obj _ N i r)) ≪≫
          e.shift d a N i r).hom =
      ((e.val.evaluate d).mapIso (eqToIso (inputShift_obj _ K i r)) ≪≫
          e.shift d a K i r).hom ≫ ((e.val.evaluate d).map f)⟦r⟧' := by
  classical
  obtain ⟨j, hj⟩ := e.property.surjective i
  obtain ⟨α, hα⟩ := shift_witness d a i r e.val e.property.injective j hj
  have hcomp (P : ∀ k, C (X k).left) :
      ((e.val.evaluate d).mapIso (eqToIso (inputShift_obj _ P i r)) ≪≫
        e.shift d a P i r).hom = α.hom.app P := by
    obtain ⟨c, hc, h0, hs, hh⟩ := hα P
    have hc' : e.variableContext d P i = c := by
      simp [IndependentExpression.variableContext, hc]
    subst c
    apply eq_of_heq
    apply HEq.trans (b := ((e.variableContext d P i).shift a r (P i)).hom)
    · simp only [IndependentExpression.shift, Iso.trans_hom, Functor.mapIso_hom,
        Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_map]
      simp
    · exact hh.symm
  rw [hcomp N, hcomp K]
  exact α.hom.naturality f

end WeilConjectures.IntegralSystemRealization
