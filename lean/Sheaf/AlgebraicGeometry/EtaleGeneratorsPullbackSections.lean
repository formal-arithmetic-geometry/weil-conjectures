/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleIsoTorsor

/-! # Pullback of generator sections

Source: Stacks Project, Tags 040E and 0097.
(blueprint: lem-sc-etale-generators-pullback-section)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pull a trivialisation back along the first projection and identify the result
with the restriction of tensor pullback. All data are explicit composites of
pullback, its structure-module isomorphism, and composition comparisons.
Source: Stacks Project, Tags 040E and 0097.
(blueprint: lem-sc-etale-generators-pullback-section) -/
noncomputable def etaleGeneratorsPullbackSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)]
    (W : X.Etale) (s : (etaleIsoTorsor L).sheaf.obj.obj (op W)) :
    (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf.obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) := by
  haveI : IsIso s.down.1 := s.down.2
  let comparison : tensorPullback f ≅ pullback f :=
    (Classical.choice (nonempty_tensorPullbackAdjunction f)).leftAdjointUniq
      (pullbackPushforwardAdjunction f)
  let p := Limits.pullback.fst W.hom f
  let q := Limits.pullback.snd W.hom f
  let e : (pullback q).obj (unit Y) ≅
      (pullback q).obj ((tensorPullback f).obj L) :=
    pullbackObjUnitIso q ≪≫ (pullbackObjUnitIso p).symm ≪≫
      (pullback p).mapIso (pullbackObjUnitIso W.hom).symm ≪≫
      (pullback p).mapIso (asIso s.down.1) ≪≫
      (pullbackComp p W.hom).app L ≪≫
      (pullbackCongr Limits.pullback.condition).app L ≪≫
      ((pullbackComp q f).app L).symm ≪≫
      (pullback q).mapIso (comparison.app L).symm
  exact ⟨⟨e.hom, (inferInstance : IsIso e.hom)⟩⟩

end AlgebraicGeometry.Scheme.Modules
