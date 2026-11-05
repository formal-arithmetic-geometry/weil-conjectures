/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionForgetIsoTransport

/-! # Normalization of a transported pushforward comparison -/

@[expose] public section

namespace CategoryTheory

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {I : C ⥤ D} {I' : C' ⥤ D'} {NC FC : C ⥤ C'} {ND FD : D ⥤ D'}

lemma projectionPushForgetIso_hom_app_of_factorization
    (δ : I ⋙ ND ≅ NC ⋙ I') (aC : NC ≅ FC) (aD : ND ≅ FD) (M : C)
    (d : FD.obj (I.obj M) ⟶ I'.obj (FC.obj M))
    (h : δ.hom.app M = aD.hom.app (I.obj M) ≫ d ≫ I'.map (aC.inv.app M)) :
    (projectionPushForgetIso δ aC aD).hom.app M = d := by
  simp only [projectionPushForgetIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app]
  rw [h]
  simp [Category.assoc, ← Functor.map_comp]

end CategoryTheory
