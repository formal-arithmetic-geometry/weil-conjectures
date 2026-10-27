/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Restriction normalization of binary comparison composites

Source: blueprint main-20261015, `det-prop-scalar-six-pullback`, proof (2),
compatibility with composition; the explicit categorical calculation extracted in
(blueprint: lem-sfb-normalized-comparison-binary-restriction).

The restriction identifications remain arbitrary specified natural isomorphisms.
Equations are written componentwise, equivalently as equalities of natural transformations.
-/

@[expose] public section

set_option autoImplicit false

universe vXr vSr vTr vXs vSs vTs uXr uSr uTr uXs uSs uTs

namespace CategoryTheory

variable {Xr : Type uXr} [Category.{vXr} Xr]
  {Sr : Type uSr} [Category.{vSr} Sr] {Tr : Type uTr} [Category.{vTr} Tr]
  {Xs : Type uXs} [Category.{vXs} Xs]
  {Ss : Type uSs} [Category.{vSs} Ss] {Ts : Type uTs} [Category.{vTs} Ts]

/-- The specified binary comparison H, with explicit functor associators.
Source: blueprint main-20261015, `det-prop-scalar-six-pullback`, proof (2).
(blueprint: lem-sfb-normalized-comparison-binary-restriction). -/
def binaryComparisonComposite
    {Ear : Sr ⥤ Xr} {Ebr : Tr ⥤ Sr} {Eas : Ss ⥤ Xs} {Ebs : Ts ⥤ Ss}
    {FX : Xr ⥤ Xs} {FS : Sr ⥤ Ss} {FT : Tr ⥤ Ts}
    (ha : Ear ⋙ FX ≅ FS ⋙ Eas) (hb : Ebr ⋙ FS ≅ FT ⋙ Ebs) :
    (Ebr ⋙ Ear) ⋙ FX ≅ (FT ⋙ Ebs) ⋙ Eas :=
  Functor.associator Ebr Ear FX ≪≫ Functor.isoWhiskerLeft Ebr ha ≪≫
    (Functor.associator Ebr FS Eas).symm ≪≫ Functor.isoWhiskerRight hb Eas

/-- The iterated restriction normalization eta, with explicit associators and unitors.
Source: blueprint main-20261015, `det-prop-scalar-six-pullback`, proof (2).
(blueprint: lem-sfb-normalized-comparison-binary-restriction). -/
def binaryRestrictionCounit
    {La : Xr ⥤ Sr} {Lb : Sr ⥤ Tr} {Ea : Sr ⥤ Xr} {Eb : Tr ⥤ Sr}
    (ra : Ea ⋙ La ≅ 𝟭 Sr) (rb : Eb ⋙ Lb ≅ 𝟭 Tr) :
    (Eb ⋙ Ea) ⋙ (La ⋙ Lb) ≅ 𝟭 Tr :=
  (Functor.associator (Eb ⋙ Ea) La Lb).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator Eb Ea La) Lb ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft Eb ra) Lb ≪≫
    Functor.isoWhiskerRight (Functor.rightUnitor Eb) Lb ≪≫ rb

/-- The comparison transported by the two specified extension compositors.
Source: blueprint main-20261015, `det-prop-scalar-six-pullback`, proof (2).
(blueprint: lem-sfb-normalized-comparison-binary-restriction). -/
def binaryComparisonTransport
    {Ear : Sr ⥤ Xr} {Ebr : Tr ⥤ Sr} {Eabr : Tr ⥤ Xr}
    {Eas : Ss ⥤ Xs} {Ebs : Ts ⥤ Ss} {Eabs : Ts ⥤ Xs}
    {FX : Xr ⥤ Xs} {FS : Sr ⥤ Ss} {FT : Tr ⥤ Ts}
    (ha : Ear ⋙ FX ≅ FS ⋙ Eas) (hb : Ebr ⋙ FS ≅ FT ⋙ Ebs)
    (gr : Ebr ⋙ Ear ≅ Eabr) (gs : Ebs ⋙ Eas ≅ Eabs) :
    Eabr ⋙ FX ≅ FT ⋙ Eabs :=
  Functor.isoWhiskerRight gr.symm FX ≪≫ binaryComparisonComposite ha hb ≪≫
    Functor.associator FT Ebs Eas ≪≫ Functor.isoWhiskerLeft FT gs

/-- Binary pasting preserves restriction normalization, and so does transport by
compatible extension compositors. No faithfulness, adjunction or geometry is assumed.

Source: blueprint main-20261015, `det-prop-scalar-six-pullback`, proof (2),
restriction calculation (G), (N), (B).
(blueprint: lem-sfb-normalized-comparison-binary-restriction).

Proof: (1) Expand H and eta at M. Apply the exchange law
`Functor.whiskerLeft_comp_whiskerRight` to hb and the s-normalization ra.
(2) Substitute the two assumed normalizations na and nb and distribute Lbs over
composition. (3) Apply exchange to qb and the r-normalization ra whiskered by Ebr.
(4) Combine the adjacent FT images to obtain exactly (B); equality at every M
is equality of natural transformations. (5) Expand the transported comparison and
use gs_compat, then (B) and q_compat, inserting the restriction identifications.
(6) Naturality of qab at gr inverse moves the inverse compositor through qab.
(7) Use gr_compat and the inverse identities of gr to cancel it. This gives the
second normalization at every M. Whiskering and composition of the given natural
isomorphisms supply the actual isomorphism binaryComparisonTransport. -/
theorem normalizedComparison_binary_restriction
    (Lar : Xr ⥤ Sr) (Lbr : Sr ⥤ Tr) (Labr : Xr ⥤ Tr)
    (Las : Xs ⥤ Ss) (Lbs : Ss ⥤ Ts) (Labs : Xs ⥤ Ts)
    (Ear : Sr ⥤ Xr) (Ebr : Tr ⥤ Sr) (Eabr : Tr ⥤ Xr)
    (Eas : Ss ⥤ Xs) (Ebs : Ts ⥤ Ss) (Eabs : Ts ⥤ Xs)
    (rar : Ear ⋙ Lar ≅ 𝟭 Sr) (rbr : Ebr ⋙ Lbr ≅ 𝟭 Tr)
    (rabr : Eabr ⋙ Labr ≅ 𝟭 Tr)
    (ras : Eas ⋙ Las ≅ 𝟭 Ss) (rbs : Ebs ⋙ Lbs ≅ 𝟭 Ts)
    (rabs : Eabs ⋙ Labs ≅ 𝟭 Ts)
    (cr : Labr ≅ Lar ⋙ Lbr) (cs : Labs ≅ Las ⋙ Lbs)
    (gr : Ebr ⋙ Ear ≅ Eabr) (gs : Ebs ⋙ Eas ≅ Eabs)
    (gr_compat : ∀ M : Tr,
      Labr.map (gr.hom.app M) ≫ rabr.hom.app M =
        cr.hom.app (Ear.obj (Ebr.obj M)) ≫
          Lbr.map (rar.hom.app (Ebr.obj M)) ≫ rbr.hom.app M)
    (gs_compat : ∀ M : Ts,
      Labs.map (gs.hom.app M) ≫ rabs.hom.app M =
        cs.hom.app (Eas.obj (Ebs.obj M)) ≫
          Lbs.map (ras.hom.app (Ebs.obj M)) ≫ rbs.hom.app M)
    (FX : Xr ⥤ Xs) (FS : Sr ⥤ Ss) (FT : Tr ⥤ Ts)
    (qa : FX ⋙ Las ≅ Lar ⋙ FS) (qb : FS ⋙ Lbs ≅ Lbr ⋙ FT)
    (qab : FX ⋙ Labs ≅ Labr ⋙ FT)
    (q_compat : ∀ M : Xr,
      qab.hom.app M ≫ FT.map (cr.hom.app M) =
        cs.hom.app (FX.obj M) ≫ Lbs.map (qa.hom.app M) ≫ qb.hom.app (Lar.obj M))
    (ha : Ear ⋙ FX ≅ FS ⋙ Eas) (hb : Ebr ⋙ FS ≅ FT ⋙ Ebs)
    (na : ∀ M : Sr,
      Las.map (ha.hom.app M) ≫ ras.hom.app (FS.obj M) =
        qa.hom.app (Ear.obj M) ≫ FS.map (rar.hom.app M))
    (nb : ∀ M : Tr,
      Lbs.map (hb.hom.app M) ≫ rbs.hom.app (FT.obj M) =
        qb.hom.app (Ebr.obj M) ≫ FT.map (rbr.hom.app M)) :
    (∀ M : Tr,
      Lbs.map (Las.map ((binaryComparisonComposite ha hb).hom.app M)) ≫
          (binaryRestrictionCounit ras rbs).hom.app (FT.obj M) =
        Lbs.map (qa.hom.app (Ear.obj (Ebr.obj M))) ≫
          qb.hom.app (Lar.obj (Ear.obj (Ebr.obj M))) ≫
          FT.map ((binaryRestrictionCounit rar rbr).hom.app M)) ∧
    (∀ M : Tr,
      Labs.map ((binaryComparisonTransport ha hb gr gs).hom.app M) ≫
          rabs.hom.app (FT.obj M) =
        qab.hom.app (Eabr.obj M) ≫ FT.map (rabr.hom.app M)) := by
  have hbinary : ∀ M : Tr,
      Lbs.map (Las.map ((binaryComparisonComposite ha hb).hom.app M)) ≫
          (binaryRestrictionCounit ras rbs).hom.app (FT.obj M) =
        Lbs.map (qa.hom.app (Ear.obj (Ebr.obj M))) ≫
          qb.hom.app (Lar.obj (Ear.obj (Ebr.obj M))) ≫
          FT.map ((binaryRestrictionCounit rar rbr).hom.app M) := by
    intro M
    simp only [Functor.comp_obj, Functor.id_obj, binaryComparisonComposite, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp, Functor.map_comp, binaryRestrictionCounit,
      Functor.map_id, Functor.rightUnitor_hom_app, Category.assoc]
    have hras := congrArg (fun f ↦ Lbs.map f) (ras.hom.naturality (hb.hom.app M))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hras
    simp only [Functor.map_comp] at hras
    rw [← Category.assoc (Lbs.map (Las.map (Eas.map (hb.hom.app M)))), hras]
    simp only [Category.assoc]
    rw [← Category.assoc (Lbs.map (Las.map (ha.hom.app (Ebr.obj M)))),
      ← Lbs.map_comp, na, Lbs.map_comp]
    simp only [Category.assoc]
    rw [nb]
    have hqb := qb.hom.naturality (rar.hom.app (Ebr.obj M))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hqb
    rw [← Category.assoc (Lbs.map (FS.map (rar.hom.app (Ebr.obj M)))), hqb]
    simp only [Category.assoc]
  refine ⟨hbinary, ?_⟩
  intro M
  have hB := hbinary M
  simp only [Functor.comp_obj, Functor.id_obj, binaryRestrictionCounit, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.map_id, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.id_comp,
    Functor.map_comp] at hB
  simp only [binaryComparisonTransport, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.comp_obj, Functor.map_comp, Category.id_comp, Category.assoc]
  rw [gs_compat]
  have hcs := cs.hom.naturality ((binaryComparisonComposite ha hb).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hcs
  rw [← Category.assoc (Labs.map ((binaryComparisonComposite ha hb).hom.app M)), hcs]
  simp only [Category.assoc]
  rw [hB]
  have hq := congrArg
    (fun f ↦ f ≫ FT.map (Lbr.map (rar.hom.app (Ebr.obj M))) ≫ FT.map (rbr.hom.app M))
    (q_compat (Ear.obj (Ebr.obj M)))
  simp only [Category.assoc] at hq
  rw [← hq]
  have hqab := qab.hom.naturality (gr.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hqab
  rw [← Category.assoc (Labs.map (FX.map (gr.inv.app M))), hqab]
  simp only [Category.assoc]
  rw [← FT.map_comp, ← FT.map_comp, ← FT.map_comp, ← gr_compat]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp]

end CategoryTheory
