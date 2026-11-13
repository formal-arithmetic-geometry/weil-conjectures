/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Transport of terminal sections through inverse-image composition

Source: Stacks Project, Sites, Tags 03CB and 03CC.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The isomorphism between terminal sections of the inverse image along `k = t ≫ e` and of the
composite of inverse images, via the inverse-image composition isomorphism. No morphism in the
triangle needs to be étale (Stacks, Tags 03CB and 03CC). -/
noncomputable def etaleSetTerminalTransport
    {R S T : Scheme.{u}} (e : S ⟶ R) (t : T ⟶ S) (k : T ⟶ R)
    (hk : t ≫ e = k) (H : Sheaf R.smallEtaleTopology (Type (u + 1))) :
    ((Scheme.etaleSetPullback k).obj H).obj.obj (op (Scheme.Etale.mk (𝟙 T))) ≅
      ((Scheme.etaleSetPullback t).obj ((Scheme.etaleSetPullback e).obj H)).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ t).obj
          (Scheme.Etale.mk (𝟙 S)))) :=
  (eqToIso (congrArg (fun f : T ⟶ R ↦
    ((Scheme.etaleSetPullback f).obj H).obj.obj (op (Scheme.Etale.mk (𝟙 T)))) hk)).symm ≪≫
  (asIso (((Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T e t).hom.app
    H).hom.app (op (Scheme.Etale.mk (𝟙 T))))).symm ≪≫
  ((Scheme.etaleSetPullback t).obj ((Scheme.etaleSetPullback e).obj H)).obj.mapIso
    (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) t))
      (Category.comp_id _)).op

end AlgebraicGeometry
