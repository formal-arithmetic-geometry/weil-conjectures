/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.DualizableEvaluationCriterion
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparisonDual
import WeilConjectures.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms

/-! # Perfect RHom tensor comparison

## References

* Stacks Project, Cohomology, Tags 08DQ, 0FPC and 0GM7.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem isIso_adjunct_evaluation
    {C : Type*} [Category C] [MonoidalCategory C]
    (K D H : C) [ExactPairing K D]
    (e : ∀ A : C, (A ⟶ H) ≃ (A ⊗ K ⟶ 𝟙_ C))
    (he : ∀ (A B : C) (f : A ⟶ B) (q : B ⟶ H),
      e A (f ≫ q) = (f ⊗ₘ 𝟙 K) ≫ e B q) :
    IsIso ((e D).symm (ExactPairing.evaluation K D)) := by
  apply isIso_of_yoneda_map_bijective
  intro A
  let t : (A ⟶ D) ≃ (A ⊗ K ⟶ 𝟙_ C) :=
    (Iso.homCongr (Iso.refl A) (λ_ D).symm).trans
      (tensorRightHomEquiv A K D (𝟙_ C)).symm
  have ht (f : A ⟶ D) : t f = (f ⊗ₘ 𝟙 K) ≫ ExactPairing.evaluation K D := by
    dsimp [t, Iso.homCongr, tensorRightHomEquiv]
    simp only [Category.id_comp, comp_whiskerRight, tensorHom_id]
    monoidal
  have h (f : A ⟶ D) :
      f ≫ (e D).symm (ExactPairing.evaluation K D) = (e A).symm (t f) := by
    apply (e A).injective
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ht]
  have hf : (fun f ↦ f ≫ (e D).symm (ExactPairing.evaluation K D)) =
      ⇑(t.trans (e A).symm) := by
    funext f
    exact h f
  rw [hf]
  exact (t.trans (e A).symm).bijective

private theorem isIso_adjunct_left_evaluation
    {C : Type*} [Category C] [MonoidalCategory C]
    (K D H : C) [ExactPairing K D]
    (e : ∀ A : C, (A ⟶ H) ≃ (D ⊗ A ⟶ 𝟙_ C))
    (he : ∀ (A B : C) (f : A ⟶ B) (q : B ⟶ H),
      e A (f ≫ q) = (𝟙 D ⊗ₘ f) ≫ e B q) :
    IsIso ((e K).symm (ExactPairing.evaluation K D)) := by
  apply isIso_of_yoneda_map_bijective
  intro A
  let t : (A ⟶ K) ≃ (D ⊗ A ⟶ 𝟙_ C) :=
    (Iso.homCongr (Iso.refl A) (ρ_ K).symm).trans
      (tensorLeftHomEquiv A K D (𝟙_ C)).symm
  have ht (f : A ⟶ K) : t f = (𝟙 D ⊗ₘ f) ≫ ExactPairing.evaluation K D := by
    dsimp [t, Iso.homCongr, tensorLeftHomEquiv]
    simp only [Category.id_comp, whiskerLeft_comp, id_tensorHom]
    monoidal
  have h (f : A ⟶ K) :
      f ≫ (e K).symm (ExactPairing.evaluation K D) = (e A).symm (t f) := by
    apply (e A).injective
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ht]
  have hf : (fun f ↦ f ≫ (e K).symm (ExactPairing.evaluation K D)) =
      ⇑(t.trans (e A).symm) := by
    funext f
    exact h f
  rw [hf]
  exact (t.trans (e A).symm).bijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- The shared derived tensor instances make the witness and pairing elaboration expensive.
/-- The dual of a perfect complex is perfect, with evaluation, coevaluation, biduality,
base change, and the tensor--internal-Hom comparison.
(Stacks, Tags 08DQ, 0FPC, 0GM7) -/
theorem perfect_rhom_tensor_comparison
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K M : schemeDerivedQCohCategory X)
    (hK : Scheme.IsPerfect X K.obj)
    (adj : ∀ A B C : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)) ≃ (A ⊗ B ⟶ C))
    (hadj : ∀ (A A' B B' C C' : schemeDerivedCategory X)
      (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)),
      adj A' B' C' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ adj A B C f ≫ c)
    (adj' : ∀ A B C : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)) ≃ (B ⊗ A ⟶ C))
    (hadj' : ∀ (A A' B B' C C' : schemeDerivedCategory X)
      (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)),
      adj' A' B' C' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (b ⊗ₘ a) ≫ adj' A B C f ≫ c) :
    ∃ (Kdual : schemeDerivedQCohCategory X)
      (hdual : Kdual.obj =
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op K.obj, 𝟙_ (schemeDerivedCategory X)))
      (ev : Kdual.obj ⊗ K.obj ⟶ 𝟙_ (schemeDerivedCategory X)),
      ev = adj Kdual.obj K.obj (𝟙_ (schemeDerivedCategory X)) (eqToHom hdual) ∧
      Scheme.IsPerfect X Kdual.obj ∧
      ∃ comparison : ∀ N : schemeDerivedQCohCategory X, N.obj ⊗ Kdual.obj ⟶
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).obj (op K.obj, N.obj),
        (∀ N, adj (N.obj ⊗ Kdual.obj) K.obj N.obj (comparison N) =
            (α_ N.obj Kdual.obj K.obj).hom ≫ N.obj ◁ ev ≫ (ρ_ N.obj).hom) ∧
        IsIso (comparison M) ∧ IsIso (comparison K) ∧
        ∃ bidual : K.obj ⟶
            (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj (op Kdual.obj, 𝟙_ (schemeDerivedCategory X)),
          adj' K.obj Kdual.obj (𝟙_ (schemeDerivedCategory X)) bidual = ev ∧
          IsIso bidual ∧
          ∃ η : 𝟙_ (schemeDerivedCategory X) ⟶ K.obj ⊗ Kdual.obj,
            adj (𝟙_ (schemeDerivedCategory X)) K.obj K.obj
                (η ≫ comparison K) = (λ_ K.obj).hom ∧
            (∀ z : 𝟙_ (schemeDerivedCategory X) ⟶ K.obj ⊗ Kdual.obj,
              adj (𝟙_ (schemeDerivedCategory X)) K.obj K.obj
                  (z ≫ comparison K) = (λ_ K.obj).hom → z = η) ∧
            (∃ p : ExactPairing K.obj Kdual.obj,
              p.evaluation' = ev ∧ p.coevaluation' = η) ∧
            ∀ (T : Scheme.{u}) (g : T ⟶ X)
              [HasDerivedCategory.{w}
                (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
              (adjT : ∀ A B C : schemeDerivedCategory T,
                (A ⟶ (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
                  T.toRingedSpace.sheaf).obj (op B, C)) ≃ (A ⊗ B ⟶ C)),
              (∀ (A A' B B' C C' : schemeDerivedCategory T)
                (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
                (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
                  T.toRingedSpace.sheaf).obj (op B, C)),
                adjT A' B' C' (a ≫ f ≫
                  (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
                    T.toRingedSpace.sheaf).map (b.op, c)) =
                  (a ⊗ₘ b) ≫ adjT A B C f ≫ c) →
              ∀ m : (derivedPullback g).CoreMonoidal,
              IsDerivedPullbackMonoidalModel g m →
              ∃ bc : (derivedPullback g).obj Kdual.obj ⟶
                  (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
                    T.toRingedSpace.sheaf).obj
                    (op ((derivedPullback g).obj K.obj), 𝟙_ (schemeDerivedCategory T)),
                adjT ((derivedPullback g).obj Kdual.obj) ((derivedPullback g).obj K.obj)
                  (𝟙_ (schemeDerivedCategory T)) bc =
                    (m.μIso Kdual.obj K.obj).hom ≫ (derivedPullback g).map ev ≫
                      m.εIso.inv ∧
                IsIso bc := by
  classical
  obtain ⟨D, hD, hperfect⟩ := exists_perfect_rhom_dual X K hK
  let ev := adj D.obj K.obj (𝟙_ (schemeDerivedCategory X)) (eqToHom hD)
  let φ := fun N : schemeDerivedCategory X ↦
    (adj (N ⊗ D.obj) K.obj N).symm
      ((α_ N D.obj K.obj).hom ≫ N ◁ ev ≫ (ρ_ N).hom)
  let bidual := (adj' K.obj D.obj (𝟙_ (schemeDerivedCategory X))).symm ev
  have hφ := perfect_rhom_evaluation_isomorphisms X K hK adj hadj D.obj hD
  have : ∀ N, IsIso (φ N) := hφ
  let η := (adj (𝟙_ (schemeDerivedCategory X)) K.obj K.obj).symm
    ((λ_ K.obj).hom) ≫ inv (φ K.obj)
  have hη : η ≫ φ K.obj =
      (adj (𝟙_ (schemeDerivedCategory X)) K.obj K.obj).symm ((λ_ K.obj).hom) := by
    simp [η]
  obtain ⟨hleft, hright⟩ := dualizable_evaluation_criterion X K.obj D.obj adj hadj
    ev φ hφ (fun N ↦ by simp only [φ, id_tensorHom]) η hη
  let p : ExactPairing K.obj D.obj :=
    { evaluation' := ev
      coevaluation' := η
      coevaluation_evaluation' := by
        have h := congrArg (fun f ↦ (ρ_ D.obj).hom ≫ f ≫ (λ_ D.obj).inv) hright
        simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp,
          Iso.hom_inv_id, Category.comp_id, tensorHom_def, id_tensorHom,
          tensorHom_id, whiskerLeft_id, id_whiskerRight] using h.symm
      evaluation_coevaluation' := by
        have h := congrArg (fun f ↦ (λ_ K.obj).hom ≫ f ≫ (ρ_ K.obj).inv) hleft
        simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp,
          Iso.hom_inv_id, Category.comp_id, tensorHom_def, id_tensorHom,
          tensorHom_id, whiskerLeft_id, id_whiskerRight] using h.symm }
  have hb : IsIso bidual := by
    let := p
    apply isIso_adjunct_left_evaluation K.obj D.obj _
      (fun A ↦ adj' A D.obj (𝟙_ (schemeDerivedCategory X)))
    intro A B f q
    have hh := hadj' B A D.obj D.obj (𝟙_ (schemeDerivedCategory X))
      (𝟙_ (schemeDerivedCategory X)) f (𝟙 _) (𝟙 _) q
    have hmap := (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).map_id (op D.obj, 𝟙_ (schemeDerivedCategory X))
    rw [op_id, ← prod_id', hmap] at hh
    simpa only [Category.comp_id, id_tensorHom] using hh
  refine ⟨D, hD, ev, rfl, hperfect, (fun N ↦ φ N.obj), ?_, hφ M.obj,
    hφ K.obj, bidual, ?_, hb, η, ?_, ?_, ⟨p, rfl, rfl⟩, ?_⟩
  · intro N
    exact (adj (N.obj ⊗ D.obj) K.obj N.obj).apply_symm_apply _
  · exact (adj' K.obj D.obj (𝟙_ (schemeDerivedCategory X))).apply_symm_apply ev
  · rw [hη]
    exact (adj (𝟙_ (schemeDerivedCategory X)) K.obj K.obj).apply_symm_apply _
  · intro z hz
    apply (cancel_mono (φ K.obj)).1
    apply (adj (𝟙_ (schemeDerivedCategory X)) K.obj K.obj).injective
    rw [hz, hη]
    exact ((adj (𝟙_ (schemeDerivedCategory X)) K.obj K.obj).apply_symm_apply _).symm
  · intro T g _ adjT hadjT m hm
    let bc := (adjT ((derivedPullback g).obj D.obj) ((derivedPullback g).obj K.obj)
      (𝟙_ (schemeDerivedCategory T))).symm
        ((m.μIso D.obj K.obj).hom ≫ (derivedPullback g).map ev ≫ m.εIso.inv)
    refine ⟨bc, ?_, ?_⟩
    · exact (adjT ((derivedPullback g).obj D.obj) ((derivedPullback g).obj K.obj)
        (𝟙_ (schemeDerivedCategory T))).apply_symm_apply _
    · let := p
      let := m.toMonoidal
      let := ExactPairing.map (derivedPullback g) K.obj D.obj
      apply isIso_adjunct_evaluation ((derivedPullback g).obj K.obj)
        ((derivedPullback g).obj D.obj) _
        (fun A ↦ adjT A ((derivedPullback g).obj K.obj)
          (𝟙_ (schemeDerivedCategory T)))
      intro A B f q
      have hh := hadjT B A ((derivedPullback g).obj K.obj)
        ((derivedPullback g).obj K.obj) (𝟙_ (schemeDerivedCategory T))
        (𝟙_ (schemeDerivedCategory T)) f (𝟙 _) (𝟙 _) q
      have hmap := (derivedInternalHom (Opens.grothendieckTopology T.toRingedSpace)
        T.toRingedSpace.sheaf).map_id
        (op ((derivedPullback g).obj K.obj), 𝟙_ (schemeDerivedCategory T))
      rw [op_id, ← prod_id', hmap] at hh
      simpa only [Category.comp_id, tensorHom_id] using hh

end AlgebraicGeometry
