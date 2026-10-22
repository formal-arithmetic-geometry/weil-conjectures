/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
import Sheaf.CategoryTheory.SystemEvaluationTopos

/-! # Modules over a constant sequence of coefficient sheaves

Source: Stacks Project, Tags 03DA and 0940; the constant-coefficient case of
Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})

private abbrev system :=
  SheafOfModules.StrictRingSystem.{u, u, u} (J := J) ((Functor.const ℕᵒᵖ).obj O)

private def toTower : system O ⥤ (ℕᵒᵖ ⥤ Mod O) where
  obj M :=
    { obj n := M.level n.unop
      map h := M.transition (leOfHom h.unop)
      map_id n := by
        ext U x
        exact M.identity n.unop U x
      map_comp f g := by
        ext U x
        exact M.compose (leOfHom g.unop) (leOfHom f.unop) U x }
  map f :=
    { app n := f.app n.unop
      naturality := by
        intro n m h
        exact (f.comm (leOfHom h.unop)).symm }
  map_id M := rfl
  map_comp f g := rfl

private def fromTower : (ℕᵒᵖ ⥤ Mod O) ⥤ system O where
  obj F :=
    { level n := F.obj (op n)
      transition h := F.map (homOfLE h).op
      identity n U x := by
        have h := congrArg (fun f ↦ f.val.app U) (F.map_id (op n))
        exact ConcreteCategory.congr_hom h x
      compose h k U x := by
        have h := congrArg (fun f ↦ f.val.app U)
          (F.map_comp (homOfLE k).op (homOfLE h).op)
        exact ConcreteCategory.congr_hom h x }
  map f :=
    { app n := f.app (op n)
      comm := by
        intro n m h
        exact (f.naturality (homOfLE h).op).symm }
  map_id F := rfl
  map_comp f g := rfl

set_option maxHeartbeats 800000 in
-- Identity restrictions reduce through the varying-ring system interface.
private def systemTowerEquivalence : system O ≌ (ℕᵒᵖ ⥤ Mod O) where
  functor := toTower O
  inverse := fromTower O
  unitIso := NatIso.ofComponents (fun M ↦
    { hom := { app n := 𝟙 _
               comm := by intros; ext U x; rfl }
      inv := { app n := 𝟙 _
               comm := by intros; ext U x; rfl }
      hom_inv_id := by
        apply SheafOfModules.strictRingSystem_hom_ext
        intro n
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp
      inv_hom_id := by
        apply SheafOfModules.strictRingSystem_hom_ext
        intro n
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp })
    (by
      intro M N f
      apply SheafOfModules.strictRingSystem_hom_ext
      intro n
      change f.app n ≫ 𝟙 _ = 𝟙 _ ≫ f.app n
      simp)
  counitIso := NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun n ↦ Iso.refl _)
    (by
      intro n m h
      change F.map _ ≫ 𝟙 _ = 𝟙 _ ≫ F.map h
      simp only [Category.comp_id, Category.id_comp])) (by intro M N f; ext n; exact rfl)
  functor_unitIso_comp M := by ext n; simp [toTower]

private theorem identityRestriction_hom_heq {R : Type u} [Ring R]
    (φ : R →+* R) (hφ : φ = RingHom.id R) (M N : ModuleCat.{u} R)
    (f : M ⟶ N) (g : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    (h : ∀ x : M, f x = g x) : HEq f g := by
  subst φ
  apply heq_of_eq
  ext x
  exact h x

/-- Modules over a constant coefficient sequence are ordinary module towers, with the
literal component sections, vertical restrictions, horizontal restrictions and maps.

Source: Stacks Project, Tags 03DA and 0940; Zheng, Construction 4.1
(blueprint: lem-pur-constant-sequence-module-equivalence).

Proof: the existing strict-system/sequence-site equivalence restricts modules to slices
and obtains their transitions from horizontal arrows. For a constant coefficient diagram,
restriction along every coefficient arrow is restriction along the identity; hence its
strict semilinear systems are ordinary diagrams of modules. Conversely an ordinary tower
supplies the levels and transitions of a strict system. Both round trips have identity
component maps. Compose these equivalences. The formulas for sections and maps are
literal identities, and additivity holds componentwise. -/
theorem constantSequenceModuleEquivalence :
    ∃ E : Mod (SheafOfModules.systemSequenceRing.{u, u, u} (J := J) ((Functor.const ℕᵒᵖ).obj O)) ≌
        (ℕᵒᵖ ⥤ Mod O),
      E.functor.Additive ∧
      (∀ (M : Mod (SheafOfModules.systemSequenceRing.{u, u, u} (J := J)
          ((Functor.const ℕᵒᵖ).obj O)))
        (n : ℕ) (U : Cᵒᵖ),
        HEq (((E.functor.obj M).obj (op n)).val.obj U) (M.val.obj (op (n, U.unop)))) ∧
      (∀ (M : Mod (SheafOfModules.systemSequenceRing.{u, u, u} (J := J)
          ((Functor.const ℕᵒᵖ).obj O)))
        (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V),
        HEq (((E.functor.obj M).obj (op n)).val.map f)
          (M.val.map (Prod.mkHom (𝟙 n) f.unop).op)) ∧
      (∀ (M : Mod (SheafOfModules.systemSequenceRing.{u, u, u} (J := J)
          ((Functor.const ℕᵒᵖ).obj O)))
        {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
        HEq (((E.functor.obj M).map (homOfLE h).op).val.app U)
          (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)) ∧
      (∀ {M N : Mod (SheafOfModules.systemSequenceRing.{u, u, u} (J := J)
          ((Functor.const ℕᵒᵖ).obj O))}
        (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
        HEq (((E.functor.map f).app (op n)).val.app U) (f.val.app (op (n, U.unop)))) := by
  let E := (SheafOfModules.strictSystemSequenceEquivalence.{u, u, u} (J := J)
    ((Functor.const ℕᵒᵖ).obj O)).symm.trans (systemTowerEquivalence O)
  have : (toTower O).Additive := by
    constructor
    intro M N f g
    apply NatTrans.ext
    funext n
    change (SheafOfModules.systemEvaluation ((Functor.const ℕᵒᵖ).obj O) n.unop).map
      (f + g) = _
    exact (SheafOfModules.systemEvaluation ((Functor.const ℕᵒᵖ).obj O) n.unop).map_add
  have hE : E.functor.Additive := by
    change ((SheafOfModules.sequenceToStrictSystemFunctor.{u, u, u} (J := J)
      ((Functor.const ℕᵒᵖ).obj O)) ⋙ toTower O).Additive
    infer_instance
  refine ⟨E, hE, ?_, ?_, ?_, ?_⟩
  · intro M n U
    rfl
  · intro M n U V f
    rfl
  · intro M m n h U
    change HEq
      (SheafOfModules.sequenceSystemTransitionApp ((Functor.const ℕᵒᵖ).obj O) M h U)
      (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
    let φ := ((SheafOfModules.derivedChangeRingIndependentCoefficients
      (WeilConjectures.coefficientSequenceTopology J)
      (SheafOfModules.systemSequenceRing.{u, u, u} (J := J)
        ((Functor.const ℕᵒᵖ).obj O))).obj.map
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom
    have hφ : φ = RingHom.id _ := by
      have hh := SheafOfModules.systemSequenceRing_horizontal
        ((Functor.const ℕᵒᵖ).obj O) h U
      dsimp only [Functor.const_obj_map] at hh
      exact congrArg (fun t ↦ t.hom) hh
    exact identityRestriction_hom_heq φ hφ _ _ _ _ (fun x ↦ rfl)
  · intro M N f n U
    rfl

end CategoryTheory.ConstantCompletion
