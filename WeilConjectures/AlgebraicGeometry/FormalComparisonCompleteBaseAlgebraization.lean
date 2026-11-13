/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.FormalComparisonAlgebraizationQuotientLift
import WeilConjectures.AlgebraicGeometry.AffineCompleteCoherentSections
import WeilConjectures.AlgebraicGeometry.ProperCompleteQuotientSectionsJointlyMonic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Algebraization of the comparison over a complete affine base

## References

* Stacks Project, Tags 088B, 087W and 0883
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over a complete Noetherian affine base the formal comparison is the completion
of an algebraic adjunction map, followed by the pushforward of an isomorphism
(Stacks, Tag 088B; Tags 087W and 0883). -/
theorem formalComparison_complete_base_algebraization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    {Z : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of A)) [IsProper p]
    (adj : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
    (G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (F : CoherentModules Z)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback p ≅
      formalCompletionSystem (J.comap p) F.obj)
    (h : RingedSpace.IsCoherent (Spec (CommRingCat.of A)).toRingedSpace
      ((Scheme.Modules.pushforward p).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward p).obj F.obj) ⟶
      formalCompletionSystem (J.comap p) F.obj ⋙ Scheme.Modules.pushforward p)
    (α : G ⟶ (completion _ J).obj ⟨(Scheme.Modules.pushforward p).obj F.obj, h⟩)
    (hKappa : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward p).obj F.obj) ≫
        κ.app (op n) = (Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (J.comap p) (n + 1) F.obj))
    (hAlpha : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward p).map (β.hom.app (op n))) :
    ∃ (A₀ : CoherentModules (Spec (CommRingCat.of A)))
      (b : (Scheme.Modules.tensorPullback p).obj A₀.obj ≅ F.obj),
    ∃ eA : limit (G.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A)) ≅
        (moduleSpecΓFunctor (R := CommRingCat.of A)).obj A₀.obj,
    ∃ eD : limit (((completion _ J).obj
        ⟨(Scheme.Modules.pushforward p).obj F.obj, h⟩).obj ⋙
          moduleSpecΓFunctor (R := CommRingCat.of A)) ≅
        (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
          ((Scheme.Modules.pushforward p).obj F.obj),
      lim.map (Functor.whiskerRight α.hom
        (moduleSpecΓFunctor (R := CommRingCat.of A))) ≫ eD.hom =
      eA.hom ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        (adj.unit.app A₀.obj ≫ (Scheme.Modules.pushforward p).map b.hom) := by
  obtain ⟨A₀, e, b, hb⟩ :=
    formalComparison_algebraization_quotient_lift I J hJ p G F β
  obtain ⟨sA, hsA⟩ := affine_complete_coherent_sections I J hJ A₀
  obtain ⟨sD, hsD⟩ := affine_complete_coherent_sections I J hJ
    ⟨(Scheme.Modules.pushforward p).obj F.obj, h⟩
  let Γ := moduleSpecΓFunctor (R := CommRingCat.of A)
  let eG := HasLimit.isoOfNatIso (Functor.isoWhiskerRight e Γ)
  let eA := eG ≪≫ sA.symm
  refine ⟨A₀, b, eA, sD.symm, ?_⟩
  apply (cancel_epi eA.inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply proper_complete_quotient_sections_jointly_monic I J hJ p F
  intro n
  have heA : eA.inv ≫ limit.π (G.obj ⋙ Γ) (op n) =
      Γ.map (formalModuleQuotientπ J (n + 1) A₀.obj) ≫
        Γ.map (e.inv.app (op n)) := by
    dsimp only [eA, eG, Iso.trans_inv, Iso.symm_inv]
    rw [Category.assoc, HasLimit.isoOfNatIso_inv_π, ← Category.assoc, hsA]
    rfl
  have hq := congrArg Γ.map (hKappa n)
  rw [Γ.map_comp] at hq
  have hα := congrArg Γ.map (hAlpha n)
  rw [Γ.map_comp, Γ.map_comp] at hα
  have hn := adj.unit.naturality
    (formalModuleQuotientπ J (n + 1) A₀.obj ≫ e.inv.app (op n))
  change (formalModuleQuotientπ J (n + 1) A₀.obj ≫ e.inv.app (op n)) ≫
      adj.unit.app (G.obj.obj (op n)) =
    adj.unit.app A₀.obj ≫ (Scheme.Modules.pushforward p).map
      ((Scheme.Modules.tensorPullback p).map
        (formalModuleQuotientπ J (n + 1) A₀.obj ≫ e.inv.app (op n))) at hn
  have hn' : (formalModuleQuotientπ J (n + 1) A₀.obj ≫ e.inv.app (op n)) ≫
      (adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward p).map (β.hom.app (op n))) =
    (adj.unit.app A₀.obj ≫ (Scheme.Modules.pushforward p).map b.hom) ≫
      (Scheme.Modules.pushforward p).map
        (formalModuleQuotientπ (J.comap p) (n + 1) F.obj) := by
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
      Functor.map_comp (Scheme.Modules.tensorPullback p), Category.assoc, hb n,
      Functor.map_comp, Category.assoc]
  calc
    _ = eA.inv ≫ lim.map (Functor.whiskerRight α.hom Γ) ≫
        sD.inv ≫ Γ.map (formalModuleQuotientπ J (n + 1)
          ((Scheme.Modules.pushforward p).obj F.obj)) ≫ Γ.map (κ.app (op n)) := by
      simp only [Category.assoc, hq]
      rfl
    _ = eA.inv ≫ lim.map (Functor.whiskerRight α.hom Γ) ≫
        limit.π (formalCompletionSystem J
          ((Scheme.Modules.pushforward p).obj F.obj) ⋙ Γ) (op n) ≫
          Γ.map (κ.app (op n)) := by
      rw [← hsD n]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    _ = (eA.inv ≫ limit.π (G.obj ⋙ Γ) (op n)) ≫
        Γ.map (α.hom.app (op n)) ≫ Γ.map (κ.app (op n)) := by
      change eA.inv ≫ limMap (Functor.whiskerRight α.hom Γ) ≫ _ ≫ _ = _
      have ht := limMap_π (Functor.whiskerRight α.hom Γ) (op n)
      simpa only [Category.assoc, Functor.whiskerRight_app, completion,
        ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj,
        formalCompletionFunctor] using
        congrArg (fun t ↦ eA.inv ≫ t ≫ Γ.map (κ.app (op n))) ht
    _ = Γ.map (formalModuleQuotientπ J (n + 1) A₀.obj) ≫
        Γ.map (e.inv.app (op n)) ≫ Γ.map (adj.unit.app (G.obj.obj (op n))) ≫
          Γ.map ((Scheme.Modules.pushforward p).map (β.hom.app (op n))) := by
      rw [heA]
      simp only [Category.assoc, hα]
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc] using congrArg Γ.map hn'

end AlgebraicGeometry
