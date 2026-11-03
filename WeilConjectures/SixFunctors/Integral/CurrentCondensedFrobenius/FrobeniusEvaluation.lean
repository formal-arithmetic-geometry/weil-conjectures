/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed

/-! # Evaluation for the canonical contragredient Weil datum

Source: current blueprint, `sk-thm-frobenius.proof.md`, first paragraph
(blueprint: lem-pod-current-contragredient-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.SixFunctors.CurrentCondensedFrobenius

section
universe v w
variable {C : Type v} [Category.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  (F : C ⥤ C) [F.Monoidal] [F.IsEquivalence]

private def dualReturn (X : C) (phi : F.obj X ≅ X) :
    F.obj ((ihom X).obj (𝟙_ _)) ≅ (ihom X).obj (𝟙_ _) :=
  Functor.Monoidal.ihomObjIso F X (𝟙_ _) ≪≫
    (ihom (F.obj X)).mapIso (Functor.Monoidal.εIso F).symm ≪≫
      (MonoidalClosed.internalHom.mapIso phi.symm.op).app (𝟙_ _)

private theorem evaluation_equivariant (X : C) (phi : F.obj X ≅ X) :
    (phi.hom ⊗ₘ (dualReturn F X phi).hom) ≫ (ihom.ev X).app (𝟙_ _) =
      (Functor.Monoidal.μIso F X _).hom ≫ F.map ((ihom.ev X).app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso F).inv := by
  dsimp only [dualReturn, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [MonoidalCategory.tensorHom_def, whiskerLeft_comp, Category.assoc]
  erw [id_tensor_pre_app_comp_ev]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.op_hom, Iso.symm_hom, Quiver.Hom.unop_op,
    Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  rw [ihom.ev_naturality]
  erw [Functor.LaxMonoidal.ihomComparison_ev_assoc]
  rfl


end

/-- The recorded contragredient datum makes evaluation equivariant.
Source: `sk-thm-frobenius.proof.md`, naturality of evaluation
(blueprint: lem-pod-current-contragredient-evaluation).

Proof: expand the closed monoidal comparison. Naturality of evaluation in its
first argument moves the inverse Weil map to that argument, where it cancels
the Weil map. Naturality in the value argument moves the unit comparison past
evaluation. The remaining equality is the evaluation equation for the canonical
internal-Hom comparison of the monoidal pullback equivalence. -/
theorem contragredientEvaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}} (g : T ≅ T)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)))
    (phi : (StrictWeilCondensed.action Λ g).obj K ≅ K) :
    (phi.hom ⊗ₘ (StrictWeilCondensed.dualDatum Λ g K phi).hom) ≫
        (ihom.ev K).app (𝟙_ _) =
      (Functor.Monoidal.μIso (StrictWeilCondensed.action Λ g) K _).hom ≫
        (StrictWeilCondensed.action Λ g).map ((ihom.ev K).app (𝟙_ _)) ≫
          (Functor.Monoidal.εIso (StrictWeilCondensed.action Λ g)).inv := by
  simpa only [StrictWeilCondensed.dualDatum, dualReturn] using
    evaluation_equivariant (StrictWeilCondensed.action Λ g) K phi

end WeilConjectures.SixFunctors.CurrentCondensedFrobenius
