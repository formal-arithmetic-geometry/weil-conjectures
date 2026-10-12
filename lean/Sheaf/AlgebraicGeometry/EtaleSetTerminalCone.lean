/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetTerminalTransport
public import Sheaf.AlgebraicGeometry.EtaleSetTerminalRestriction
public import Sheaf.AlgebraicGeometry.EtaleSetSectionComparison

/-! # Compatibility of terminal section identifications

Source: Stacks Project, Tags 03S2, 03CB and 03CC.
(blueprint: lem-weil-pbc-sets-terminal-cone).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 03S2 and Sites Tags 03CB and 03CC;
the canonical comparison calculation in the degree-zero route of Tag 09YQ.
(blueprint: lem-weil-pbc-sets-terminal-cone).

Proof: Expand terminal transport and section comparison. The composition-unit
equation for the structure morphism of `W` and the map to `W` identifies the
iterated pulled-back section with the section pulled back along `p`. The
restriction-unit equation at the étale object `U` identifies the input section
with its restriction to the terminal object over `U`. Naturality of both units
moves this section through the comparison. Associativity of inverse-image
composition makes the two composition isomorphisms agree. After cancelling
these isomorphisms, the two maps of pullbacks have first projection `t` and
second projection the identity, so pullback uniqueness identifies both with the
explicit diagonal lift below. Equality transports depend only on their endpoints.
No étaleness assumption is used on `p`, `t` or `t₀`; thus identity maps, empty
schemes and arbitrary cone legs are included. -/
theorem etaleSetTerminalCone
    {R T : Scheme.{u}} (H : Sheaf R.smallEtaleTopology (Type (u + 1)))
    (U W : R.Etale) (q : U ⟶ W) (p : T ⟶ R) (t : T ⟶ U.left) (t₀ : T ⟶ W.left)
    (ht : t ≫ q.left = t₀) (hp : t ≫ U.hom = p) (hp₀ : t₀ ≫ W.hom = p) :
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
      (R.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale)).unit.app H).hom.app (op U)) ≫
        ((Scheme.etaleSetPullback p).obj H).obj.map
          (MorphismProperty.Over.homMk
            (B := (MorphismProperty.Over.pullback @Etale ⊤ p).obj U)
            (pullback.lift t (𝟙 _) (by simpa using hp))
            (pullback.lift_snd _ _ _)).op ≫
        (etaleSetTerminalTransport W.hom t₀ p hp₀ H).hom =
      (etaleSetTerminalRestriction H U ≪≫
        etaleSetTerminalTransport W.hom q.left U.hom (MorphismProperty.Over.w q) H).hom ≫
      etaleSetSectionComparison t q.left t₀ ht
        ((Scheme.etaleSetPullback W.hom).obj H) (Scheme.Etale.mk (𝟙 W.left)) := by sorry

end AlgebraicGeometry
