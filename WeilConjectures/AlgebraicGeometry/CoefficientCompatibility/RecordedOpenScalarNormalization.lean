/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarRealizationTransport
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarSiteTransport
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarCounitSquare

/-! # Realization normalization for the open scalar factor

Source: Stacks Tags 00YV, 03DI and 07A6; the open-factor argument in
`lem-sp-recorded-compact-scalar-fixed-normalization`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] proEtaleConstantRingMap scalarExtensionFunctor

end AlgebraicGeometry.ProEtale.CoefficientCompatibility

namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

private theorem conjugated_scalar_unit
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ C') (F : D ≌ D')
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (r : F.functor ⋙ R' ≅ R ⋙ E.functor)
    (M : C) :
    E.functor.map (a.unit.app M) ≫ r.inv.app (L.obj M) =
      b.unit.app (E.functor.obj M) ≫ R'.map
        ((((E.toAdjunction.comp b).ofNatIsoRight
          (isoWhiskerRight F.counitIso.symm (R' ⋙ E.inverse) ≪≫
            isoWhiskerLeft F.inverse (isoWhiskerRight r E.inverse) ≪≫
            isoWhiskerLeft (F.inverse ⋙ R) E.unitIso.symm)).leftAdjointUniq
          (a.comp F.toAdjunction)).hom.app M) := by
  apply comparison_unit E F a b _ r
  intro N
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
    Functor.comp_map, Functor.comp_obj, Category.assoc]
  have hη := E.unitIso.hom.naturality (R.map (F.unitIso.hom.app N))
  have hr := r.inv.naturality (F.unitIso.hom.app N)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hη hr
  rw [reassoc_of% hη, ← E.inverse.map_comp_assoc, hr]
  simp only [Functor.map_comp, Category.assoc]
  rw [← E.inverse.map_comp, ← R'.map_comp]
  simp only [F.functor_unitIso_comp, Functor.id_obj]
  erw [R'.map_id, E.inverse.map_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
