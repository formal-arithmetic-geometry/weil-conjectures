/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses

/-!
# Evaluation preserves flat semilinear systems

Source: Zheng, Construction 4.1, and Stacks Project, Tag 08FC.
(blueprint: lem-pur-system-evaluation-flat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
private theorem evaluation_ring_app (n : ℕ) (U : Cᵒᵖ) :
    (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U =
      𝟙 ((ring.{c, v, max c v r} J (B n)).obj.obj U) := by
  change ((sheafToPresheaf J RingCat.{max c v r}).map
    (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm)).app U = _
  rw [eqToHom_map, eqToHom_app]
  rfl

private theorem evaluation_smul (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (U : Cᵒᵖ) (a : (B n).obj.obj U) (x : M.val.obj (op (n, U.unop))) :
    (a • (show ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U from x)) =
      ((show (systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop)) from a) • x
        : M.val.obj (op (n, U.unop))) := by
  change (show (systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop)) from
    ((eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U).hom a) • x = _
  erw [evaluation_ring_app.{c, v, r} J B τ n U]
  rfl

private theorem evaluation_ring_map (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop))) :
    (systemRing.{c, v, max c v r} J B τ).obj.map ((Prod.sectR n C).map f.unop).op a =
      (B n).obj.map f (show (B n).obj.obj U from a) := by
  have hn := (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.naturality f
  erw [evaluation_ring_app.{c, v, r} J B τ n U,
    evaluation_ring_app.{c, v, r} J B τ n V] at hn
  erw [Category.comp_id, Category.id_comp] at hn
  exact RingHom.congr_fun (congrArg RingCat.Hom.hom hn.symm) a

private def evaluationCoefficientEquiv (n : ℕ) (U : Cᵒᵖ) :
    (B n).obj.obj U ≃+*
      (systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop)) := RingEquiv.refl _

private def evaluationSectionEquiv (n : ℕ)
    (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ) :
    ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U ≃+
      M.val.obj (op (n, U.unop)) := AddEquiv.refl _

private theorem evaluationSectionEquiv_smul (n : ℕ)
    (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (a : (B n).obj.obj U)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    evaluationSectionEquiv.{c, v, r} J B τ n M U (a • x) =
      evaluationCoefficientEquiv.{c, v, r} J B τ n U a •
        evaluationSectionEquiv.{c, v, r} J B τ n M U x :=
  evaluation_smul.{c, v, r} J B τ n M U a x

private theorem evaluationSectionEquiv_map (n : ℕ)
    (M : Systems.{c, v, max c v r} J B τ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    evaluationSectionEquiv.{c, v, r} J B τ n M V
      (((evaluation.{c, v, max c v r} J B τ n).obj M).val.map f x) =
      M.val.map ((Prod.sectR n C).map f.unop).op
        (evaluationSectionEquiv.{c, v, r} J B τ n M U x) := rfl

private theorem evaluationCoefficientEquiv_map (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (B n).obj.obj U) :
    evaluationCoefficientEquiv.{c, v, r} J B τ n V ((B n).obj.map f a) =
      (systemRing.{c, v, max c v r} J B τ).obj.map ((Prod.sectR n C).map f.unop).op
        (evaluationCoefficientEquiv.{c, v, r} J B τ n U a) :=
  (evaluation_ring_map.{c, v, r} J B τ n f a).symm

attribute [local irreducible] evaluation evaluationCoefficientEquiv evaluationSectionEquiv

/-- Evaluation preserves flatness on the coefficient sequence site.
Source: Zheng, Construction 4.1, and Stacks Project, Tag 08FC
(blueprint: lem-pur-system-evaluation-flat).
Proof: test the local finite-relation criterion at an object U of the original site.
Identify evaluated sections and scalars with those of the system at (n,U).
Apply flatness on the sequence site to this finite relation. Its covering sieve pulls
back along the vertical inclusion to a covering sieve of U, by the definition of the
sequence topology. Restrict its finite factorization witnesses to vertical arrows.
The coefficient and additive section identifications preserve restriction, scalar
multiplication, finite sums and products, so these are the required witnesses on U.
The argument also applies to empty finite families and empty covering sieves. -/
theorem evaluation_preserves_flat (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (hM : SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := coefficientSequenceTopology J) (R := systemRing J B τ) M) :
    SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := B n) ((evaluation.{c, v, max c v r} J B τ n).obj M) := by
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion.{c, v, max c v r, max c v r}
    (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
  intro U t a s hs
  have hs' := congrArg (evaluationSectionEquiv.{c, v, r} J B τ n M (op U)) hs
  simp only [map_sum, map_zero, evaluationSectionEquiv_smul.{c, v, r} J B τ n M (op U)] at hs'
  obtain ⟨S, hS, h⟩ :=
    SheafOfModules.local_equationalCriterion_of_isFlatOnSite.{c, v, max c v r, max c v r}
      (systemRing.{c, v, max c v r} J B τ) M hM (n, U) t
      (fun p ↦ evaluationCoefficientEquiv.{c, v, r} J B τ n (op U) (a p))
      (fun p ↦ evaluationSectionEquiv.{c, v, r} J B τ n M (op U) (s p)) hs'
  refine ⟨S.functorPullback (Prod.sectR n C), hS, ?_⟩
  intro V f hf
  obtain ⟨l, b, z, hz, hb⟩ := h (n, V) ((Prod.sectR n C).map f) hf
  refine ⟨l, (fun p q ↦ (evaluationCoefficientEquiv.{c, v, r} J B τ n (op V)).symm (b p q)),
    (fun q ↦ (evaluationSectionEquiv.{c, v, r} J B τ n M (op V)).symm (z q)), ?_, ?_⟩
  · intro p
    apply (evaluationSectionEquiv.{c, v, r} J B τ n M (op V)).injective
    simp only [map_sum, evaluationSectionEquiv_smul.{c, v, r} J B τ n M (op V),
      AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      evaluationSectionEquiv_map.{c, v, r} J B τ n M f.op]
    exact hz p
  · intro q
    apply (evaluationCoefficientEquiv.{c, v, r} J B τ n (op V)).injective
    simp only [map_sum, map_mul, map_zero, RingEquiv.apply_symm_apply,
      evaluationCoefficientEquiv_map.{c, v, r} J B τ n f.op]
    exact hb q
end WeilConjectures.SemilinearSections
