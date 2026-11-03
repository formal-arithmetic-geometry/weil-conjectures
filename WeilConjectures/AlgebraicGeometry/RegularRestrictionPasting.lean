/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularComparisonEtaleRestrictionData

import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import all WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingCocycleSourceEtale

/-! # Pasting the specified exceptional restriction comparisons

(blueprint: lem-pur-regular-restriction-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open FiniteEtaleNormalization

set_option maxHeartbeats 1600000 in
-- Elaborating naturality through the derived functors needs this larger limit.
/-- The specified exceptional restriction comparison is compatible with a further
etale square, on the full derived categories.

Proof: expand the two successive five-factor words. Naturality
moves each rho past the neighboring exceptional compositor. Associativity of
the exceptional compositors combines the inner composition words, including
the congruences induced by the two commuting squares. The composition law for
the adjunction-normalized etale rho identifies the two remaining etale words
with rho for the composites. The residual source and target maps are precisely
the two canonical derived-pullback compositors in the statement. Cancellation
of the adjacent isomorphism/inverse pairs proves equality of the natural
isomorphisms. This computation is natural in every object, so it also holds
outside the constructible subcategory; the unbounded etale sum adjunction
normalization gives the same rho composition formula on that whole category.
Source: regular-immersion proof Step 4(i)--(ii), further restriction
(blueprint: lem-pur-regular-restriction-pasting). -/
theorem regularRestrictionPasting
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U V : Scheme.{u}}
    (i : Z ⟶ X) (uMap : U ⟶ X) (v : V ⟶ Z) (iU : V ⟶ U)
    (hcart : iU ≫ uMap = v ≫ i)
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [IsSeparated (V ↘ Spec (.of P.field.k))]
    [i.IsOver (Spec (.of P.field.k))] [uMap.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] [iU.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated uMap] [LocallyOfFiniteType uMap] [QuasiCompact uMap]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsSeparated iU] [LocallyOfFiniteType iU] [QuasiCompact iU]
    [Etale uMap] [Etale v] [IsClosedImmersion i] [IsClosedImmersion iU] :
    regularRestrictionFurtherRestriction P i uMap v iU hcart := by
  intro U' V' w t iU' hw
  intros
  apply Iso.ext
  ext K
  simp only [regularRestrictionBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  apply (cancel_mono
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) t v (t ≫ v) rfl).hom.app
      ((exceptional P i).obj K))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [finiteEtaleRho_comp, finiteEtaleRho_comp_inv]
  simp only [Functor.map_comp, Category.assoc]
  apply congrArg (fun q ↦ (exceptional P iU').map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      w uMap (w ≫ uMap) rfl).hom.app K) ≫ q)
  apply congrArg (fun q ↦ (exceptional P iU').map
    ((rho P w).inv.app ((pull P uMap).obj K)) ≫ q)
  rw [← (rho P t).hom.naturality_assoc]
  rw [← (rho P t).hom.naturality_assoc]
  rw [← (rho P t).hom.naturality_assoc]
  rw [← (rho P t).hom.naturality_assoc]
  erw [Category.comp_id]
  simp only [← Category.assoc]
  apply congrArg (fun q ↦ q ≫ (pull P t).map
    ((rho P v).hom.app ((exceptional P i).obj K)))
  apply congrArg (fun q ↦ q ≫ (rho P t).hom.app
    ((exceptional P v).obj ((exceptional P i).obj K)))
  simp only [Category.assoc]
  erw [← (comp P t iU).hom.naturality_assoc]
  rw [← (FiniteEtaleNormalization.congr P (iU' ≫ w) (t ≫ iU) hw).hom.naturality_assoc]
  erw [← (comp P iU' w).inv.naturality_assoc]
  apply congrArg (fun q ↦ (exceptional P iU').map
    ((exceptional P w).map ((rho P uMap).inv.app K)) ≫ q)
  rw [← reassoc_of% (comp_assoc_rotate P iU' w uMap K)]
  rw [comp_assoc P t v i K]
  apply congrArg (fun q ↦ (comp P iU' w).inv.app ((exceptional P uMap).obj K) ≫ q)
  simp only [← Category.assoc]
  apply congrArg (fun q ↦ q ≫ (exceptional P t).map ((comp P v i).hom.app K))
  simp only [Category.assoc]
  rw [reassoc_of% (comp_assoc_middle P t iU uMap K)]
  rw [reassoc_of% (comp_congr_left_inv P (iU' ≫ w) (t ≫ iU) uMap hw K)]
  rw [← comp_congr_right P t (iU ≫ uMap) (v ≫ i) hcart K]
  apply congrArg (fun q ↦ (comp P (iU' ≫ w) uMap).inv.app K ≫ q)
  simp only [← Category.assoc]
  apply congrArg (fun q ↦ q ≫ (comp P t (v ≫ i)).hom.app K)
  simp only [congr_eqToIso, eqToIso.hom, eqToHom_app, eqToHom_trans]


end AlgebraicGeometry.Etale
