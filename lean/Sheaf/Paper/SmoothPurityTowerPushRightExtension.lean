/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Paper.SmoothPurityTowerInjectiveComponents
public import Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Ordinary coefficient-tower inverse-image ingredients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {T S : Scheme.{t}} (g : T ⟶ S)

private def restrictionIdentity (X : Scheme.{t}) (n : ℕ) :
    systemRestriction (spCoefficientCommRings l E X) (Nat.le_refl n) ≅ 𝟭 _ := by
  let B := spCoefficientCommRings l E X
  have hid (U : X.ProEtᵒᵖ) :
      (((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat RingCat)).map
        (B.map (homOfLE (Nat.le_refl n)).op)).hom.app U).hom = RingHom.id _ := by
    have h := (B ⋙ sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat RingCat)).map_id (op n)
    exact congrArg (fun f ↦ (f.hom.app U).hom) h
  exact NatIso.ofComponents (fun J ↦
    { hom := { val :=
        { app := fun U ↦ (ModuleCat.restrictScalarsId'App _ (hid U) (J.val.obj U)).hom
          naturality := fun f ↦ by ext x; rfl } }
      inv := { val :=
        { app := fun U ↦ (ModuleCat.restrictScalarsId'App _ (hid U) (J.val.obj U)).inv
          naturality := fun f ↦ by ext x; rfl } }
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }) (by intros; ext U x; rfl)

private def rightEvaluationIso (X : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E X) (r : SpTowerEvaluationAdjoint l E X d)
    (n : ℕ) :
    (r.right n ⋙ d.equivalence.inverse) ⋙ spCoefficientEvaluation l E X d.equivalence n ≅
      𝟭 _ := by
  let e : r.right n ⋙ systemEvaluation (spCoefficientCommRings l E X) n ≅
      systemRestriction (spCoefficientCommRings l E X) (Nat.le_refl n) :=
    eqToIso (Functor.hext (fun J ↦ r.above n n (Nat.le_refl n) J)
      (fun J K f ↦ r.mapAbove n n (Nat.le_refl n) f))
  exact Functor.isoWhiskerLeft (r.right n)
    (Functor.isoWhiskerRight d.equivalence.counitIso
      (systemEvaluation (spCoefficientCommRings l E X) n)) ≪≫ e ≪≫
    restrictionIdentity l E X n

private theorem bijective_heq.{v} {A B A' B' : Type v}
    (hA : A = A') (hB : B = B') {f : A → B} {f' : A' → B'}
    (h : HEq f f') : Function.Bijective f ↔ Function.Bijective f' := by
  subst A'
  subst B'
  cases h
  rfl

section Generic
universe a v w
variable {C : Type a} [Category.{v} C] {K : GrothendieckTopology C}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (B : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})

private theorem generic_right_transition_bijective (M : StrictRingSystem.{a, v, w} B)
    (n k : ℕ) (h : n ≤ k) (J : systemLevel.{a, v, w} B n) (U : Cᵒᵖ)
    (hA : M.level k = (systemRestriction B h).obj J)
    (hB : M.level n = (systemRestriction B (Nat.le_refl n)).obj J)
    (ht : HEq (fun x ↦ (M.transition h).val.app U x) (fun x : J.val.obj U ↦ x)) :
    Function.Bijective (fun x ↦ (M.transition h).val.app U x) := by
  have ha : ((M.level k).val.obj U : Type w) = (J.val.obj U : Type w) :=
    congrArg (fun N ↦ (N.val.obj U : Type w)) hA
  have hb : ((M.level n).val.obj U : Type w) = (J.val.obj U : Type w) :=
    congrArg (fun N ↦ (N.val.obj U : Type w)) hB
  exact (bijective_heq (f := fun x ↦ (M.transition h).val.app U x)
    (f' := fun x : J.val.obj U ↦ x) ha hb ht).2 Function.bijective_id

variable [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]

private theorem generic_transition_bijective_iso
    {M N : StrictRingSystem.{a, v, w} B} (e : M ≅ N)
    {m k : ℕ} (h : m ≤ k) (U : Cᵒᵖ)
    (hb : Function.Bijective (fun x ↦ (N.transition h).val.app U x)) :
    Function.Bijective (fun x ↦ (M.transition h).val.app U x) := by
  have hr := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation _ U).mapIso ((systemEvaluation B k).mapIso e)).hom
  have hm := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation _ U).mapIso ((systemEvaluation B m).mapIso e)).hom
  change Function.Bijective (fun x ↦ (e.hom.app k).val.app U x) at hr
  change Function.Bijective (fun x ↦ (e.hom.app m).val.app U x) at hm
  have hc : (fun x ↦ (N.transition h).val.app U ((e.hom.app k).val.app U x)) =
      (fun x ↦ (e.hom.app m).val.app U ((M.transition h).val.app U x)) := by
    funext x
    exact congrArg (fun f ↦ f.val.app U x) (e.hom.comm h)
  have hb' := hb.comp hr
  change Function.Bijective (fun x ↦ (N.transition h).val.app U
    ((e.hom.app k).val.app U x)) at hb'
  rw [hc] at hb'
  exact (Function.Bijective.of_comp_iff' hm _).mp hb'
end Generic

private theorem transported_right_transition_bijective (X : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E X) (r : SpTowerEvaluationAdjoint l E X d)
    (n k : ℕ) (h : n ≤ k)
    (J : systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E X) n)
    (U : X.ProEtᵒᵖ) :
    Function.Bijective (fun x ↦ ((d.equivalence.functor.obj
      ((r.right n ⋙ d.equivalence.inverse).obj J)).transition h).val.app U x) := by
  apply generic_transition_bijective_iso (spCoefficientCommRings l E X)
    (d.equivalence.counitIso.app _) h U
  exact generic_right_transition_bijective (spCoefficientCommRings l E X)
    ((r.right n).obj J) n k h J U (r.above n k h J)
    (r.above n n (Nat.le_refl n) J) (r.transitionAbove n n k h (Nat.le_refl n) J U)


section GenericIso
universe a v w
variable {C : Type a} [Category.{v} C] {K : GrothendieckTopology C}

private theorem sheaf_iso_of_bijective {R : Sheaf K RingCat.{w}}
    {M N : SheafOfModules.{w} R} (f : M ⟶ N)
    (hb : ∀ U : Cᵒᵖ, Function.Bijective (fun x ↦ f.val.app U x)) : IsIso f := by
  have (U : Cᵒᵖ) : IsIso (f.val.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (hb U)
  let e : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun U ↦ asIso (f.val.app U)) (fun {_ _} g ↦ f.val.naturality g)
  let e' := (SheafOfModules.fullyFaithfulForget R).preimageIso e
  have he : e'.hom = f := by ext U; rfl
  rw [← he]
  infer_instance

variable [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})

private theorem strict_iso_of_components {M N : StrictRingSystem.{a, v, w} B}
    (f : M ⟶ N) (hf : ∀ k, IsIso (f.app k)) : IsIso f := by
  let (k : ℕ) := hf k
  let g : N ⟶ M :=
    { app := fun k ↦ inv (f.app k)
      comm := fun {m k} h ↦ by
        apply (cancel_epi (f.app k)).mp
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm h]
        rw [Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id]
        rw [CategoryTheory.Functor.map_id, Category.comp_id] }
  have ext {P Q : StrictRingSystem.{a, v, w} B} (a b : P ⟶ Q)
      (h : ∀ k, a.app k = b.app k) : a = b := by
    cases a
    cases b
    congr
    exact funext h
  exact ⟨g, ext _ _ (fun k ↦ IsIso.hom_inv_id (f.app k)),
    ext _ _ (fun k ↦ IsIso.inv_hom_id (f.app k))⟩

private theorem above_map_bijective {M N : StrictRingSystem.{a, v, w} B}
    (f : M ⟶ N) {n k : ℕ} (h : n ≤ k) (U : Cᵒᵖ)
    (hf : Function.Bijective (fun x ↦ (f.app n).val.app U x))
    (hM : Function.Bijective (fun x ↦ (M.transition h).val.app U x))
    (hN : Function.Bijective (fun x ↦ (N.transition h).val.app U x)) :
    Function.Bijective (fun x ↦ (f.app k).val.app U x) := by
  have hc : (fun x ↦ (N.transition h).val.app U ((f.app k).val.app U x)) =
      (fun x ↦ (f.app n).val.app U ((M.transition h).val.app U x)) := by
    funext x
    exact congrArg (fun v ↦ v.val.app U x) (f.comm h)
  have hb := hf.comp hM
  change Function.Bijective (fun x ↦ (f.app n).val.app U
    ((M.transition h).val.app U x)) at hb
  rw [← hc] at hb
  exact (Function.Bijective.of_comp_iff' hN _).mp hb
end GenericIso

private theorem moduleHom_bijective_heq.{v, w} {R : Type w} [Ring R]
    {M M' N N' : ModuleCat.{v} R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {f' : M' ⟶ N'} (h : HEq f f') :
    Function.Bijective (fun x ↦ f x) ↔ Function.Bijective (fun x ↦ f' x) := by
  subst M'
  subst N'
  cases h
  rfl

private theorem evaluationTransition_bijective (X : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E X) (M : spCoefficientTowers l E X)
    {m k : ℕ} (h : m ≤ k) (U : X.ProEtᵒᵖ) :
    Function.Bijective (fun x ↦ ((d.equivalence.functor.obj M).transition h).val.app U x) ↔
      Function.Bijective (fun x ↦
        M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  refine moduleHom_bijective_heq
    (f := ((d.equivalence.functor.obj M).transition h).val.app U)
    (f' := M.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
    (eq_of_heq (d.sections M k U)) ?_ (d.transitions M h U)
  have hc : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((spCoefficientCommRings l E X).map (homOfLE h).op) =
      (spCoefficientRings l E X).map (homOfLE h).op := by
    let F := spCoefficientCommRings l E X ⋙ sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
    let q : F ⟶ spCoefficientRings l E X := NatTrans.ofOpSequence
      (fun _ ↦ 𝟙 _) (fun j ↦ by
        simp only [F, Functor.comp_map, spCoefficientCommRings, spCoefficientRings,
          Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp, Category.comp_id]
        rfl)
    have hh := q.naturality (homOfLE h).op
    simpa only [F, Functor.comp_obj, Functor.comp_map, q, NatTrans.ofOpSequence_app,
      Category.id_comp, Category.comp_id] using hh
  convert congrArg (ModuleCat.restrictScalars
    ((spCoefficientPresheaf l E X).map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom).obj
      (eq_of_heq (d.sections M m U)) using 1
  · simp [spCoefficientPresheaf, spCoefficientRings, spCoefficientRing,
      spCoefficientCommRings, derivedChangeRingIndependentCoefficients]
  · change (ModuleCat.restrictScalars
        (((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat RingCat)).map
            ((spCoefficientCommRings l E X).map (homOfLE h).op)).hom.app U).hom).obj _ = _
    rw [hc]
    simp [spCoefficientPresheaf, spCoefficientRings, spCoefficientRing,
      spCoefficientCommRings, derivedChangeRingIndependentCoefficients]

private theorem raw_push_transition_bijective
    (M : spCoefficientTowers l E T) {n k : ℕ} (h : n ≤ k) (U : S.ProEtᵒᵖ)
    (hb : Function.Bijective (fun x ↦ M.obj.map
      (Prod.mkHom (homOfLE h) (𝟙 ((Scheme.proEtaleBaseChange g).obj U.unop))).op x)) :
    Function.Bijective (fun x ↦ ((spTowerPush l E g).obj M).obj.map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  have hm : (spTowerBaseChange g).op.map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op =
      (Prod.mkHom (homOfLE h) (𝟙 ((Scheme.proEtaleBaseChange g).obj U.unop))).op := by
    simp [spTowerBaseChange]
  change Function.Bijective (fun x ↦ M.obj.map
    ((spTowerBaseChange g).op.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) x)
  rw [hm]
  exact hb

private theorem push_transition_bijective
    (dT : SpCoefficientTowersAbelian l E T) (dS : SpCoefficientTowersAbelian l E S)
    (M : spCoefficientTowers l E T) {n k : ℕ} (h : n ≤ k) (U : S.ProEtᵒᵖ)
    (hb : Function.Bijective (fun x ↦
      ((dT.equivalence.functor.obj M).transition h).val.app
        ((Scheme.proEtaleBaseChange g).op.obj U) x)) :
    Function.Bijective (fun x ↦
      ((dS.equivalence.functor.obj ((spTowerPush l E g).obj M)).transition h).val.app U x) := by
  apply (evaluationTransition_bijective l E S dS _ h U).2
  apply raw_push_transition_bijective l E g M h U
  exact (evaluationTransition_bijective l E T dT M h _).1 hb

private theorem transported_right_below (X : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E X) (r : SpTowerEvaluationAdjoint l E X d)
    (n k : ℕ) (h : k < n)
    (J : systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E X) n) :
    IsZero ((spCoefficientEvaluation l E X d.equivalence k).obj
      ((r.right n ⋙ d.equivalence.inverse).obj J)) := by
  exact (r.below n k h J).of_iso
    ((systemEvaluation (spCoefficientCommRings l E X) k).mapIso
      (d.equivalence.counitIso.app _))

private theorem pushed_right_below
    (dT : SpCoefficientTowersAbelian l E T) (dS : SpCoefficientTowersAbelian l E S)
    (rT : SpTowerEvaluationAdjoint l E T dT) (n k : ℕ) (h : k < n)
    (J : systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n) :
    IsZero ((spCoefficientEvaluation l E S dS.equivalence k).obj
      ((spTowerPush l E g).obj ((rT.right n ⋙ dT.equivalence.inverse).obj J))) := by
  exact ((spLevelPush l E g k).map_isZero
    (transported_right_below l E T dT rT n k h J)).of_iso
      ((spTowerEvaluationIso l E g dT dS k).app _)

/-- The zero-below, scalar-restriction-above right extensions commute with direct image.
Source: blueprint sk-lem-sp-tower-levels-adjoint.proof.md, Well-defined and Adjunction;
Stacks 03D1 (blueprint: lem-sp-tower-push-right-extension).
Proof: above n, both composites are identified sectionwise on every base-changed
pro-etale object. Their scalar actions agree by naturality of the constant-section
coefficient comparison, and their transitions are identities above n. Below n both
extensions are zero, including the boundary transition. These sectionwise identities
assemble to a natural tower isomorphism; the normalized equivalences transport it to
the recorded tower categories. -/
theorem sp_tower_push_right_extension
    (dT : SpCoefficientTowersAbelian l E T) (dS : SpCoefficientTowersAbelian l E S)
    (rT : SpTowerEvaluationAdjoint l E T dT) (rS : SpTowerEvaluationAdjoint l E S dS)
    (n : ℕ) :
    Nonempty ((rT.right n ⋙ dT.equivalence.inverse) ⋙ spTowerPush l E g ≅
      spLevelPush l E g n ⋙ (rS.right n ⋙ dS.equivalence.inverse)) := by
  let RT := rT.right n ⋙ dT.equivalence.inverse
  let RS := rS.right n ⋙ dS.equivalence.inverse
  let K := spCoefficientEvaluation l E S dS.equivalence n
  let F := RT ⋙ spTowerPush l E g
  let H := spLevelPush l E g n ⋙ RS
  let e : F ⋙ K ≅ spLevelPush l E g n :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft RT (spTowerEvaluationIso l E g dT dS n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rightEvaluationIso l E T dT rT n) _ ≪≫
      Functor.leftUnitor _
  let a := rS.adjunction n
  let v : F ⟶ H := Functor.whiskerLeft F a.unit ≫ Functor.whiskerRight e.hom RS
  have : IsIso a.counit := a.isIso_counit_of_iso (rightEvaluationIso l E S dS rS n)
  have hv (J : systemLevel.{t + 1, t, max u (t + 1)}
      (spCoefficientCommRings l E T) n) : IsIso (K.map (v.app J)) := by
    have : IsIso (K.map (a.unit.app (F.obj J))) :=
      isIso_of_comp_hom_eq_id _ (a.left_triangle_components (F.obj J))
    change IsIso (K.map (a.unit.app (F.obj J) ≫ RS.map (e.hom.app J)))
    rw [Functor.map_comp]
    infer_instance
  have hv' (J : systemLevel.{t + 1, t, max u (t + 1)}
      (spCoefficientCommRings l E T) n) : IsIso (v.app J) := by
    have := hv J
    have : IsIso (dS.equivalence.functor.map (v.app J)) := by
      apply strict_iso_of_components
      intro k
      by_cases h : n ≤ k
      · apply sheaf_iso_of_bijective
        intro U
        exact above_map_bijective (spCoefficientCommRings l E S)
          (dS.equivalence.functor.map (v.app J)) h U
          (ConcreteCategory.bijective_of_isIso
            ((SheafOfModules.evaluation _ U).map (K.map (v.app J))))
          (push_transition_bijective l E g dT dS (RT.obj J) h U
            (transported_right_transition_bijective l E T dT rT n k h J _))
          (transported_right_transition_bijective l E S dS rS n k h
            ((spLevelPush l E g n).obj J) U)
      · exact (pushed_right_below l E g dT dS rT n k (Nat.lt_of_not_ge h) J).isIso
          (transported_right_below l E S dS rS n k (Nat.lt_of_not_ge h)
            ((spLevelPush l E g n).obj J)) _
    exact isIso_of_reflects_iso (v.app J) dS.equivalence.functor
  have : IsIso v := (NatTrans.isIso_iff_isIso_app v).2 hv'
  exact ⟨asIso v⟩

end AlgebraicGeometry.ProEtale
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
