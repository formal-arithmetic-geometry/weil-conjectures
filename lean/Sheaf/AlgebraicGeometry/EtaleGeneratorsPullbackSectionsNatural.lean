/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSections

/-! # Naturality of pulled-back generator sections

Source: Stacks Project, Tags 040E and 0097.
(blueprint: lem-sc-etale-generators-pullback-sections-natural)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling back generator sections commutes with etale restrictions.
Source: Stacks Project, Tag 0097 (composition of pullbacks), Tag 040E (generators).
(blueprint: lem-sc-etale-generators-pullback-sections-natural)

Proof: Expand restriction in the presheaf of isomorphisms as conjugation by the
module pseudofunctor's composition constraints. Expand the section map as the
pullback of the trivialisation along the first projection, conjugated by the
structure-module and tensor-comparison isomorphisms. The pullback square for a
map of etale objects commutes. The associativity coherence for module pullback
then identifies the two composite comparison maps; naturality of the structure
module comparison and of the left-adjoint comparison identifies their outer
factors. The middle factors agree by functoriality of module pullback. Thus the
underlying homomorphisms agree, and subtype and ULift extensionality give equality
of generator sections. This argument includes empty objects and zero rings.
-/
theorem etaleGeneratorsPullbackSection_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)]
    {V W : X.Etale} (i : V ⟶ W)
    (s : (etaleIsoTorsor L).sheaf.obj.obj (op W)) :
    (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf.obj.map
      ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).op
      (etaleGeneratorsPullbackSection f L W s) =
    etaleGeneratorsPullbackSection f L V ((etaleIsoTorsor L).sheaf.obj.map i.op s) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
