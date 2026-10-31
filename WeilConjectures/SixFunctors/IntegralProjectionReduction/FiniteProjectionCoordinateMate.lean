/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicRealization.FiniteIntrinsicRealizationComparisons

/-! # Projection mates in inverse coefficient coordinates

Source: adjunction Hom naturality and equivalence triangle identities, Stacks 003G.
(blueprint: lem-sf-finite-projection-coordinate-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace WeilConjectures.IntegralProjectionReduction
open FiniteIntrinsicRealization

/-- Evaluate a realized composite in inverse coefficient coordinates.
Source: Stacks 003G, equivalence triangle identities.
(blueprint: lem-sf-finite-projection-coordinate-mate).

Proof: the forward image of the inverse-coordinate endpoint is the original
endpoint by naturality of the coefficient counit and its triangle identity.
Naturality of the forward functor comparison moves that endpoint through the
comparison. Naturality of the target coefficient unit then gives the formula. -/
theorem inverseComparison_evaluation
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (f : C ≌ D) (P : B ⥤ D) (Q : A ⥤ C)
    (r : e.functor ⋙ P ≅ Q ⋙ f.functor)
    {M : B} {N : A} {W : C} (t : M ⟶ e.functor.obj N) (q : Q.obj N ⟶ W) :
    f.inverse.map (P.map t ≫ r.hom.app N ≫ f.functor.map q) ≫ f.unitIso.inv.app W =
      (inverseComparison e f P Q r).hom.app M ≫
        Q.map (e.inverse.map t ≫ e.unitIso.inv.app N) ≫ q := by
  let z := e.inverse.map t ≫ e.unitIso.inv.app N
  have hz : e.counitIso.inv.app M ≫ e.functor.map z = t := by
    dsimp only [z]
    rw [Functor.map_comp, ← Category.assoc]
    erw [← e.counitIso.inv.naturality t]
    rw [Category.assoc]
    simp only [Functor.id_map, Equivalence.counitIso_functor_comp]
    exact Category.comp_id t
  have hn := r.hom.naturality z
  dsimp only [Functor.comp_map] at hn
  dsimp only [inverseComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom]
  simp only [Functor.comp_map, Category.assoc]
  change _ = f.inverse.map (P.map (e.counitIso.inv.app M)) ≫
    f.inverse.map (r.hom.app (e.inverse.obj M)) ≫
    f.unitIso.inv.app (Q.obj (e.inverse.obj M)) ≫ Q.map z ≫ q
  erw [← f.unitIso.inv.naturality_assoc]
  simp only [← f.inverse.map_comp_assoc, Functor.comp_map]
  rw [← hn, ← P.map_comp_assoc, hz]
  simp only [Functor.map_comp, Category.assoc]
  erw [f.unitIso.inv.naturality]
  rfl

end WeilConjectures.IntegralProjectionReduction

namespace WeilConjectures.IntegralProjectionReduction
open FiniteIntrinsicRealization

end WeilConjectures.IntegralProjectionReduction
