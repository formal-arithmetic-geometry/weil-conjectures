/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
public import WeilConjectures.AlgebraicGeometry.FiniteCompactSupportComparisonAgreement
public import WeilConjectures.SmoothPurity.FiniteExceptional.FiniteExceptionalHomCounitEvaluation
public import WeilConjectures.SmoothPurity.FiniteIntrinsicRealizationTPlus

/-! # Live finite exceptional comparison interface

The declarations below realize the live blueprint route, without the withdrawn
four-clause exceptional q-identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
variable (P : PurityFiniteSetting.{u}) (n m : ℕ) (h : m ≤ n)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
/-- The included finite exceptional counit is the specified intrinsic counit.
Source: blueprint finite reduction of purity, Step 4
(blueprint: lem-route-finite-reduction-exceptional-finite-model-counit-normalization).
Proof: finite-Tor constructibility makes the inverse intrinsic realization bounded
below. Apply AdjunctionNormalized to the published exceptional counit and its
etale-origin witness. Evaluation of fixedHom is the identity by right-adjoint
uniqueness. Naturality of homEquiv along the intrinsic equivalence counit and the
triangle identity identify the transpose with the identity. Transposing back gives
the included finite counit. The bounded-below branch of smoothExceptionalCounit is
exactly this composite. This is one coefficient level, with no reduction equation;
the argument applies to equal indices, zero objects, and empty schemes. -/
theorem finiteExceptionalCounit_normalization
    (L : (FiniteExceptional.domain P.coefficients.l P.extension Y n).FullSubcategory) :
    (FiniteExceptional.domain P.coefficients.l P.extension Y n).ι.map
      ((FiniteExceptional.adjunction P.coefficients.l P.extension P.field
        P.coefficients.different f (@HasCompactification.compactification X Y f
        (hasCompactification_of_finiteType_over_field P.field.k X Y f)) n).counit.app L) =
      (P.finiteReductionSetting (n + 1) (Nat.succ_pos n)).smoothExceptionalCounit
        f L.obj := by
  classical
  let l := P.coefficients.l
  let E := P.extension
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let c := @HasCompactification.compactification X Y f
    (hasCompactification_of_finiteType_over_field P.field.k X Y f)
  let EX := Scheme.sfIntrinsicDerivedEquivalence X A
  let EY := Scheme.sfIntrinsicDerivedEquivalence Y A
  let J := ProEtale.sfFiniteExceptionalFixed A c
  let a := FiniteExceptional.adjunction l E P.field P.coefficients.different f c n
  have hplus := finiteIntrinsicRealization_tplus
    (P.finiteReductionSetting (n + 1) (Nat.succ_pos n)) L
  let N : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) := ⟨EY.inverse.obj L.obj, hplus⟩
  let M := FiniteExceptional.finiteCounitSource l E P.field f c n N
  let W := FiniteExceptional.finiteCounitOriginWitness l E P.field f c n N
  let v := FiniteExceptional.finitePublishedCounitAt l E P.field f c n N
  have hM : FiniteExceptional.domain l E X n (EX.functor.obj M.obj) :=
    ((FiniteExceptional.G l E P.field P.coefficients.different f c n).obj L).property
  have : (FiniteExceptional.domain l E Y n).IsClosedUnderIsomorphisms :=
    (Scheme.finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) Y).1
  have hN : FiniteExceptional.domain l E Y n (EY.functor.obj N.obj) :=
    (FiniteExceptional.domain l E Y n).prop_of_iso (EY.counitIso.symm.app L.obj) L.property
  have heval : FiniteExceptional.fixedHom l E P.field f c n M W N v = 𝟙 M.obj := by
    let eH := FiniteExceptional.fixedHom l E P.field f c n M W N
    have hh := FiniteExceptional.finiteExceptionalHom_counit l E P.field
      P.coefficients.different f c n N
    exact (congrArg eH hh.symm).trans (eH.apply_symm_apply _)
  let t : (FiniteExceptional.F l E P.field P.coefficients.different f c n).obj
      ⟨EX.functor.obj M.obj, hM⟩ ⟶ ⟨EY.functor.obj N.obj, hN⟩ :=
    ObjectProperty.homMk
      ((ProEtale.sfIntrinsicCompactSupportComparison A c).hom.app M.obj ≫ EY.functor.map v)
  let e : (⟨EY.functor.obj N.obj, hN⟩ :
      (FiniteExceptional.domain l E Y n).FullSubcategory) ⟶ L :=
    ObjectProperty.homMk (EY.counitIso.hom.app L.obj)
  have hn : (a.homEquiv _ _ t).hom =
      EX.functor.map (J.map (EY.unitIso.hom.app N.obj)) := by
    have hn := (FiniteExceptional.adjunction_existsUnique l E P.field
      P.coefficients.different f c n).choose_spec.1 M W N hM hN v
    have hn' : (a.homEquiv _ _ t).hom =
        EX.functor.map (FiniteExceptional.fixedHom l E P.field f c n M W N v ≫
          J.map (EY.unitIso.hom.app N.obj)) := hn
    simpa only [heval, Category.id_comp] using hn'
  have ht : a.homEquiv _ L (t ≫ e) = 𝟙 _ := by
    rw [a.homEquiv_naturality_right]
    apply ObjectProperty.hom_ext
    change (a.homEquiv _ _ t).hom ≫ EX.functor.map (J.map (EY.inverse.map e.hom)) = _
    erw [hn, ← EX.functor.map_comp, ← J.map_comp]
    change EX.functor.map (J.map
      (EY.unitIso.hom.app (EY.inverse.obj L.obj) ≫
        EY.inverse.map (EY.counitIso.hom.app L.obj))) = 𝟙 _
    have htri : EY.unitIso.hom.app (EY.inverse.obj L.obj) ≫
        EY.inverse.map (EY.counitIso.hom.app L.obj) = 𝟙 _ := EY.unit_inverse_comp L.obj
    exact (congrArg (fun z ↦ EX.functor.map (J.map z)) htri).trans
      ((congrArg EX.functor.map (J.map_id _)).trans (EX.functor.map_id _))
  have hc : a.counit.app L = t ≫ e := by
    have ht' : a.homEquiv
        ((FiniteExceptional.G l E P.field P.coefficients.different f c n).obj L) L
        (t ≫ e) = 𝟙 _ := ht
    have hh := congrArg (a.homEquiv _ L).symm ht'
    exact (a.homEquiv_symm_id L).symm.trans
      (hh.symm.trans ((a.homEquiv _ L).symm_apply_apply _))
  change (a.counit.app L).hom = _
  rw [hc]
  change ((ProEtale.sfIntrinsicCompactSupportComparison A c).hom.app M.obj ≫
    EY.functor.map v) ≫ EY.counitIso.hom.app L.obj = _
  rw [Category.assoc]
  let : HasCompactification f :=
    hasCompactification_of_finiteType_over_field P.field.k X Y f
  have hcmp := (ProEtale.finiteCompactSupportComparisonAgreement P.field.k
    (X ↘ Spec (.of P.field.k)) (Y ↘ Spec (.of P.field.k)) f
    (ULift.{u + 1, u} A) c c).2.2.2.2.1
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  have hv : v = ProEtale.rightDerivedUpperShriekCounit f N.obj N.property := by
    dsimp only [v, FiniteExceptional.finitePublishedCounitAt]
    change (ProEtale.rightDerivedLowerShriekOfCompactificationOriginIso
      (ULift.{u + 1, u} A) c c).inv.app _ ≫ _ = _
    rw [hcmp]
    simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  rw [hv]
  unfold smoothExceptionalCounit
  dsimp only
  split_ifs with hL
  · rfl
  · exact (hL hplus).elim

end WeilConjectures.PurityFiniteSetting
