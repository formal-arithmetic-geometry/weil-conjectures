/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorSignedCancellation
public import WeilConjectures.Algebra.Homology.ScalarInternalHomDataSupplement
import WeilConjectures.Algebra.Homology.RingedScalarTensorShift

/-! # Opposite-shift cancellation for normalized scalar tensor comparison

Source: Stacks 06YY, 07A4, 0A8X and 08JC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor Opposite WeilConjectures SheafOfModules

namespace CategoryTheory

section Cancellation
variable {C D : Type*} [Category C] [Category D]
  [HasShift C ℤ] [HasShift D ℤ]
  (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
  [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.flip.obj K).CommShift ℤ]
  [∀ K, (S.obj K).CommShift ℤ] [∀ K, (S.flip.obj K).CommShift ℤ]
  [∀ {K L} (f : K ⟶ L), NatTrans.CommShift (S.flip.map f) ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]

private def cancelTensor (K L : C) (n : ℤ) :
    (T.obj (K⟦-n⟧)).obj (L⟦n⟧) ⟶ (T.obj K).obj L :=
  ((T.flip.obj (L⟦n⟧)).commShiftIso (-n)).hom.app K ≫
    (((T.obj K).commShiftIso n).hom.app L)⟦-n⟧' ≫
    (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app _

private theorem comparison_cancellation
    (τ : (postcompose₂.obj F).obj T ⟶
      (((whiskeringLeft₂ D).obj F).obj F).obj S)
    (hleft : ∀ K, NatTrans.CommShift
      (F₁ := T.obj K ⋙ F) (F₂ := F ⋙ S.obj (F.obj K)) (τ.app K) ℤ)
    (hright : ∀ L, NatTrans.CommShift
      (F₁ := T.flip.obj L ⋙ F) (F₂ := F ⋙ S.flip.obj (F.obj L)) (τ.flipApp L) ℤ)
    (K L : C) (n : ℤ) :
    ((τ.app (K⟦-n⟧)).app (L⟦n⟧)) ≫
      (S.map ((F.commShiftIso (-n)).hom.app K)).app (F.obj (L⟦n⟧)) ≫
      (S.obj ((F.obj K)⟦-n⟧)).map ((F.commShiftIso n).hom.app L) ≫
      cancelTensor S (F.obj K) (F.obj L) n =
    F.map (cancelTensor T K L n) ≫ (τ.app K).app L := by
  have := hleft K
  have := hright (L⟦n⟧)
  have hL := NatTrans.shift_app_comm
    (F₁ := T.obj K ⋙ F) (F₂ := F ⋙ S.obj (F.obj K)) (τ.app K) n L
  have hR := NatTrans.shift_app_comm
    (F₁ := T.flip.obj (L⟦n⟧) ⋙ F) (F₂ := F ⋙ S.flip.obj (F.obj (L⟦n⟧)))
    (τ.flipApp (L⟦n⟧)) (-n) K
  change ((T.obj K ⋙ F).commShiftIso n).hom.app L ≫
      ((τ.app K).app L)⟦n⟧' =
    (τ.app K).app (L⟦n⟧) ≫
      ((F ⋙ S.obj (F.obj K)).commShiftIso n).hom.app L at hL
  change ((T.flip.obj (L⟦n⟧) ⋙ F).commShiftIso (-n)).hom.app K ≫
      ((τ.app K).app (L⟦n⟧))⟦-n⟧' =
    (τ.app (K⟦-n⟧)).app (L⟦n⟧) ≫
      ((F ⋙ S.flip.obj (F.obj (L⟦n⟧))).commShiftIso (-n)).hom.app K at hR
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hL hR
  dsimp only [Functor.flip_obj_map] at hR
  have hN := NatTrans.shift_app_comm
    (S.flip.map ((F.commShiftIso n).hom.app L)) (-n) (F.obj K)
  simp only [Functor.flip_map_app] at hN
  dsimp only [cancelTensor]
  rw [← reassoc_of% hN]
  rw [← reassoc_of% hR]
  simp only [← Functor.map_comp_assoc]
  rw [← hL]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.commShiftIso_hom_naturality_assoc]
  have hnat := (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.naturality
    ((τ.app K).app L)
  dsimp at hnat
  rw [hnat, ← F.map_shiftFunctorCompIsoId_hom_app_assoc ((T.obj K).obj L) n (-n)]
end Cancellation

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)]
  (A : ScalarHomModels.{c, v, r, w} J)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

/-- The supplied scalar tensor comparison respects signed opposite-shift cancellation.
Source: Stacks 06YY, 07A4 and 0FNH; blueprint
 det-prop-scalar-six-tensor-hom.proof.md, Reduction.
(blueprint: lem-sfb-ringed-scalar-tensor-cancellation-Y2).

Proof: apply fixed-slot compatibility of the normalized native scalar tensor
comparison. Paste its source-slot shift equation at -n and Hom-slot equation
at n. Naturality moves the input scalar shift through the tensor shift; scalar
shift coherence cancels [n][-n]. This proves native cancellation compatibility.
Expand the conjugated scalar comparison and use naturality of the two closed
adjunction comparisons to obtain unsigned closed cancellation compatibility.
Since F is additive it preserves the common quadratic integer-unit sign.
Finally cancel mu at the shifted and unshifted pairs. No Hom comparison or
signed Hom exactness enters this argument. -/
theorem ringedScalarTensor_cancellation (μ : ScalarHomTensorComparison A a)
    [ordinaryAdditive : (A.scalar a).extension.Additive]
    [scalarShift : (A.scalar a).derived.CommShift ℤ]
    [scalarAdditive : (A.scalar a).derived.Additive]
    (hcounit : ∀ (n : ℤ) (P : HomotopyCategory (scalarModules J R) (.up ℤ)),
      (A.scalar a).derived.map ((DerivedCategory.Qh.commShiftIso n).hom.app P) ≫
        ((A.scalar a).derived.commShiftIso n).hom.app (DerivedCategory.Qh.obj P) ≫
        ((A.scalar a).counit.app P)⟦n⟧' =
      (A.scalar a).counit.app (P⟦n⟧) ≫ DerivedCategory.Qh.map
        ((((A.scalar a).extension.mapHomotopyCategory (.up ℤ)).commShiftIso n).hom.app P) ≫
        (DerivedCategory.Qh.commShiftIso n).hom.app
          (((A.scalar a).extension.mapHomotopyCategory (.up ℤ)).obj P))
    (K P : DerivedCategory (scalarModules J R)) (n : ℤ) :
    (A.closed S).tensor.map (Prod.mkHom
        (((A.scalar a).derived.commShiftIso n).hom.app P)
        (((A.scalar a).derived.commShiftIso (-n)).hom.app K)) ≫
      RingedSignedTensor.cancellation.{c, v, r, w} J S (A.closed S)
        ((A.scalar a).derived.obj K) ((A.scalar a).derived.obj P) n ≫
      μ.iso.inv.app (P, K) =
    μ.iso.inv.app (P⟦n⟧, K⟦-n⟧) ≫
      (A.scalar a).derived.map
        (RingedSignedTensor.cancellation.{c, v, r, w} J R (A.closed R) K P n) := by
  let F := (A.scalar a).derived
  letI := RingedSignedTensor.nativeTensorShift.{c, v, r, w} J R
  letI := RingedSignedTensor.nativeTensorShift.{c, v, r, w} J S
  letI (K : DerivedCategory (scalarModules J R)) :
      ((RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J R).flip.flip.obj K).CommShift ℤ :=
    inferInstanceAs
      (((RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J R).obj K).CommShift ℤ)
  letI (K : DerivedCategory (scalarModules J S)) :
      ((RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J S).flip.flip.obj K).CommShift ℤ :=
    inferInstanceAs
      (((RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J S).obj K).CommShift ℤ)
  letI : ∀ {K L : DerivedCategory (scalarModules J S)} (f : K ⟶ L),
      NatTrans.CommShift
        ((RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J S).flip.flip.map f) ℤ :=
    fun {_ _} f ↦ inferInstanceAs
      (NatTrans.CommShift ((RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J S).map f) ℤ)
  obtain ⟨hl, hr⟩ := ringedNativeScalarComparison_commShift J A a μ hcounit
  have h := comparison_cancellation
    (RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J R).flip
    (RingedSignedTensor.nativeCurriedTensor.{c, v, r, w} J S).flip F
    (ringedNativeScalarCurriedComparison J A a μ) hl hr K P n
  have hn : (ringedNativeScalarComparison J A a μ).hom.app (P⟦n⟧, K⟦-n⟧) ≫
      (RingedSignedTensor.nativeTensor J S).map (Prod.mkHom
        ((F.commShiftIso n).hom.app P) ((F.commShiftIso (-n)).hom.app K)) ≫
      RingedSignedTensor.nativeCancellation J S (F.obj K) (F.obj P) n =
    F.map (RingedSignedTensor.nativeCancellation J R K P n) ≫
      (ringedNativeScalarComparison J A a μ).hom.app (P, K) := by
    simpa only [ringedNativeScalarCurriedComparison, cancelTensor,
      RingedSignedTensor.nativeCancellation, RingedSignedTensor.nativeTensor,
      RingedSignedTensor.nativeCurriedTensor, Functor.flip_obj_obj,
      Functor.flip_obj_map, Functor.flip_map_app, curriedTensor_obj_map,
      curriedTensor_map_app, Functor.flip_flip, tensor_map, tensorHom_def', Functor.prod_obj,
      Functor.comp_obj, Functor.comp_map, Category.assoc] using h
  let χR := RingedSignedTensor.comparison.{c, v, r, w} J R (A.closed R)
  let χS := RingedSignedTensor.comparison.{c, v, r, w} J S (A.closed S)
  have hclosed : μ.iso.hom.app (P⟦n⟧, K⟦-n⟧) ≫
      (A.closed S).tensor.map (Prod.mkHom
        ((F.commShiftIso n).hom.app P) ((F.commShiftIso (-n)).hom.app K)) ≫
      (χS.hom.app ((F.obj P)⟦n⟧, (F.obj K)⟦-n⟧) ≫
        RingedSignedTensor.nativeCancellation J S (F.obj K) (F.obj P) n ≫
          χS.inv.app (F.obj P, F.obj K)) =
    F.map (χR.hom.app (P⟦n⟧, K⟦-n⟧) ≫
      RingedSignedTensor.nativeCancellation J R K P n ≫ χR.inv.app (P, K)) ≫
        μ.iso.hom.app (P, K) := by
    have hh := congrArg (fun f ↦ F.map (χR.hom.app (P⟦n⟧, K⟦-n⟧)) ≫ f ≫
      χS.inv.app (F.obj P, F.obj K)) hn
    simp only [ringedNativeScalarComparison, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.prod_obj, Category.assoc] at hh
    rw [← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, Category.id_comp] at hh
    simp only [χR, χS, F] at hh
    erw [← reassoc_of% (χS.hom.naturality (Prod.mkHom
      ((F.commShiftIso n).hom.app P) ((F.commShiftIso (-n)).hom.app K)))] at hh
    simpa only [χR, χS, F, Functor.map_comp, Category.assoc,
      Functor.comp_obj, Functor.prod_obj, Iso.hom_inv_id_app, Category.comp_id] using hh
  apply (cancel_epi (μ.iso.hom.app (P⟦n⟧, K⟦-n⟧))).1
  simp only [Iso.hom_inv_id_app_assoc]
  apply (cancel_mono (μ.iso.hom.app (P, K))).1
  simp only [RingedSignedTensor.cancellation, Linear.comp_units_smul,
    Linear.units_smul_comp, Category.assoc, Iso.inv_hom_id_app]
  simpa only [F, χR, χS, (A.scalar a).derived.map_units_smul,
    Functor.comp_obj, Functor.prod_obj, Category.assoc, Category.comp_id,
    Linear.units_smul_comp] using
    congrArg (fun f ↦ (n * (n + 1) / 2).negOnePow • f) hclosed

end CategoryTheory
