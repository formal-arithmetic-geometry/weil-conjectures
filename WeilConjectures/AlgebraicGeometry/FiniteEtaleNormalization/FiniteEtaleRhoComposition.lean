/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization

/-! # Composition of the normalized étale exceptional identification

Source: regular-immersion proof Step 4(i), composition of the étale factors.
(blueprint: lem-pur-finite-etale-rho-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

/-- The normalized étale identification respects composition at every derived object.
The proof of the normalization law uses no constructibility assumption: transport
etaleSumRightAdjoint_comp through the canonical exact/derived pullback isomorphisms,
then cancel their composite. This records that calculation on its full domain.
Source: regular-immersion proof Step 4(i), the normalized étale composition law
(blueprint: lem-pur-finite-etale-rho-composition). -/
theorem finiteEtaleRho_comp
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    {T : Scheme.{u}}
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (v : X ⟶ T) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [Etale v]
    (K : Etale.DerivedCategoryModule P.Coefficient T) :
    (rho P (e ≫ v)).hom.app K ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e v).hom.app K =
      (comp P e v).hom.app K ≫ (rho P e).hom.app ((exceptional P v).obj K) ≫
        (pull P e).map ((rho P v).hom.app K) := by
  let := fieldSchemeNoetherian P U
  let := fieldSchemeNoetherian P X
  let := compactification P e
  let := fieldSchemeNoetherian P T
  let := compactification P v
  let := compactification P (e ≫ v)
  let C := ModuleCat.{u + 1} P.Coefficient
  have hc := Etale.etaleSumRightAdjoint_comp P.Coefficient e v
    (exceptional P e) (exceptional P v) (exceptional P (e ≫ v))
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient v)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (e ≫ v)) K
  rw [← rho_exact P (e ≫ v), ← rho_exact P e, ← rho_exact P v] at hc
  simp only [
    Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at hc
  let d := (Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).app
      ((pull P v).obj K) ≪≫ (Etale.upperStar C e).mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C v).app K)
  apply (cancel_mono d.hom).1
  change _ ≫ ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).hom.app
    ((pull P v).obj K) ≫ (Etale.upperStar C e).mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C v).hom.app K)) = _
  rw [Category.assoc, pull_comp_transport P e v K]
  rw [hc]
  rw [← (Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).hom.naturality_assoc]
  simp only [Etale.etaleSumRightAdjointCompIso, comp, d, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, C, pull, Category.assoc]

/-- The inverse composition equation in the order used by exceptional restriction.
Proof: invert the preceding equation, then use naturality of rho inverse.
Source: regular-immersion proof Step 4(i), composition of the etale factors
(blueprint: lem-pur-finite-etale-rho-composition). -/
private theorem finiteEtaleRho_comp_inv
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    {T : Scheme.{u}}
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (v : X ⟶ T) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [Etale v]
    (K : Etale.DerivedCategoryModule P.Coefficient T) :
    (rho P (e ≫ v)).inv.app K =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e v).hom.app K ≫
        (rho P e).inv.app ((pull P v).obj K) ≫
        (exceptional P e).map ((rho P v).inv.app K) ≫
        (comp P e v).inv.app K := by
  have h := finiteEtaleRho_comp P e v K
  have h' := congrArg (fun q ↦
    (rho P (e ≫ v)).inv.app K ≫ q ≫
      (pull P e).map ((rho P v).inv.app K) ≫
      (rho P e).inv.app ((exceptional P v).obj K) ≫
      (comp P e v).inv.app K) h
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at h'
  simp only [(pull P e).map_id, Category.id_comp, Iso.hom_inv_id_app_assoc] at h'
  rw [(rho P e).inv.naturality_assoc] at h'
  simpa only [Iso.hom_inv_id_app, Category.comp_id] using h'.symm

end AlgebraicGeometry.ProEtale.FiniteEtaleNormalization
