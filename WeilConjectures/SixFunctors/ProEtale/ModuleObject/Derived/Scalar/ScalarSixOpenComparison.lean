/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions

/-! # The normalized ordinary open comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem scalarSixComparison_existsUnique
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (E : A ≌ C) (H : B ≌ D) {L : A ⥤ B} {R : B ⥤ A}
    {L' : C ⥤ D} {R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (r : R ⋙ E.functor ≅ H.functor ⋙ R') :
    ∃! c : L ⋙ H.functor ≅ E.functor ⋙ L',
      (mateEquiv a b (.mk _ _ _ _ c.inv)).natTrans = r.hom := by
  let β : TwoSquare R H.functor E.functor R' := .mk _ _ _ _ r.hom
  let α := (mateEquiv a b).symm β
  have hγ : IsIso (mateEquiv H.toAdjunction E.toAdjunction β).natTrans := by
    simp only [mateEquiv_apply]
    infer_instance
  have hα : IsIso α.natTrans := by
    have h := iterated_mateEquiv_conjugateEquiv a b E.toAdjunction H.toAdjunction α
    have : IsIso (conjugateEquiv (a.comp H.toAdjunction)
        (E.toAdjunction.comp b) α.natTrans) := by
      rw [← h]
      simpa only [α, Equiv.apply_symm_apply] using hγ
    exact conjugateEquiv_of_iso (a.comp H.toAdjunction)
      (E.toAdjunction.comp b) α.natTrans
  refine ⟨(asIso α.natTrans).symm, ?_, ?_⟩
  · exact congrArg TwoSquare.natTrans ((mateEquiv a b).apply_symm_apply β)
  · intro c hc
    apply Iso.ext_inv
    change c.inv = α.natTrans
    have h : mateEquiv a b (.mk _ _ _ _ c.inv) = β := by
      ext M
      exact congr_app hc M
    exact congrArg TwoSquare.natTrans ((mateEquiv a b).eq_symm_apply.mpr h)

/-- Any fixed normalized geometric comparison transports the actual open adjunction.

Source: blueprint det-prop-scalar-six-pullback.proof.md, (2), specified open comparison;
Stacks Tags 03DI and 0B65. (blueprint: lem-sfb-scalar-six-open-comparison).

Proof: the geometric pullback comparison identifies the right adjoints after the
fixed section-module equivalences. Uniqueness of left adjoints gives the open
extension comparison. The Hom-transposition equation for this unique comparison
says exactly that its inverse mate is the specified geometric pullback hom. -/
theorem scalarSixOpenComparison_exists (E : LocallyClosedExtensionData.{u})
    (G : ScalarSixGeometry.{u}) (k : Type u) [Field k] :
    Nonempty (ScalarSixOpenComparison E G k) := by
  classical
  have h (Λ : ScalarSixRing.{u}) {S X : Over (Spec (.of k))}
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (j : S ⟶ X) [IsOpenImmersion j.left] :=
    scalarSixComparison_existsUnique
      (ModuleRingedComparison.equivalence Λ.X S.left)
      (ModuleRingedComparison.equivalence Λ.X X.left)
      (openImmersionLowerShriekUpperStarAdjunction Λ.X j.left)
      (E.openAdjunction (scalarSixImmersion G Λ j)
        (inferInstanceAs (IsOpenImmersion j.left))) (G.pull Λ j.left)
  exact ⟨{
    comparison := fun Λ _ _ _ _ _ _ _ _ j _ ↦ (h Λ j).exists.choose
    normalization := fun Λ _ _ _ _ _ _ _ _ j _ ↦ (h Λ j).exists.choose_spec }⟩

end AlgebraicGeometry.ProEtale.CondensedRing
