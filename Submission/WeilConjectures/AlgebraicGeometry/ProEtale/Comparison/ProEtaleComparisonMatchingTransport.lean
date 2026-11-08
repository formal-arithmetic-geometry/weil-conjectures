/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Transport of matching families to fpqc descent data

Source: Stacks Project, Tag 0GLZ, first paragraph; Tag 09XN.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable abbrev L {S T : Scheme.{u}} (f : T ⟶ S) :=
  Scheme.etaleSetPullback f

private noncomputable abbrev b {S T : Scheme.{u}} (f : T ⟶ S) :=
  MorphismProperty.Over.pullback @Etale ⊤ f

private abbrev Γ {S : Scheme.{u}} (H : Sheaf S.smallEtaleTopology (Type (u + 1))) :=
  H.obj.obj (op (Scheme.Etale.mk (𝟙 S)))

private noncomputable abbrev η {S T : Scheme.{u}} (f : T ⟶ S) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b f) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)).unit

-- The base change of an identity is terminal, with its explicit inverse pullback lift.
private noncomputable def terminalLift {S T : Scheme.{u}} (f : T ⟶ S) :
    Scheme.Etale.mk (𝟙 T) ⟶ (b f).obj (Scheme.Etale.mk (𝟙 S)) :=
  MorphismProperty.Over.homMk
    (pullback.lift f (𝟙 T) ((Category.comp_id _).trans (Category.id_comp _).symm))
    (by simp)

-- Inverse-image restriction evaluated on terminal sections.
private noncomputable def res {S T : Scheme.{u}} (f : T ⟶ S)
    (H : Sheaf S.smallEtaleTopology (Type (u + 1))) : Γ H ⟶ Γ ((L f).obj H) :=
  ((η f).app H).hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫
    ((L f).obj H).obj.map (terminalLift f).op

private noncomputable abbrev c {R S T : Scheme.{u}} (e : S ⟶ R) (f : T ⟶ S) :=
  Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T e f

-- Terminal transport after cancelling the second-projection isomorphism.
private noncomputable def tr {R S T : Scheme.{u}}
    (e : S ⟶ R) (f : T ⟶ S) (k : T ⟶ R) (hk : f ≫ e = k)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    Γ ((L k).obj H) ≅ Γ ((L f).obj ((L e).obj H)) :=
  (eqToIso (congrArg (fun k ↦ Γ ((L k).obj H)) hk)).symm ≪≫
    (asIso (((c e f).hom.app H).hom.app (op (Scheme.Etale.mk (𝟙 T))))).symm

end AlgebraicGeometry
