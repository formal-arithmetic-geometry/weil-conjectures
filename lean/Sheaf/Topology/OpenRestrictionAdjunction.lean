/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Topology.Sheaves.Module
import Sheaf.Paper.DerivedHomMayerVietoris

/-!
# The sectionwise open-restriction adjunction for module sheaves

Source: Stacks Project, Sheaves, Tags 0096, 00A0, 00A1 and 0095
(blueprint: lem-weil-pbc-ringed-space-open-restriction-adjunction).

We use the site `Over U`, whose objects are precisely opens of `X` contained in `U`.
The ring sheaf is the landed `AlgebraicGeometry.moduleRings X` of the ringed space.
It is equivalent to the opens of the topological subspace by `U.overEquivalence`;
`U.sheafOfModulesEquivOver` identifies the module categories. No new restriction
or direct-image functor is defined here.
-/

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace TopologicalSpace.Opens

/-- The adjunction for restriction of module sheaves to an open, with its specified
bijection and inverse. Source: Stacks Project, Tags 0096, 00A0, 00A1, 0095
(blueprint: lem-weil-pbc-ringed-space-open-restriction-adjunction).

Proof (the node's six steps):
1. Restriction retains sections, module actions, and restriction maps on opens contained
   in `U`. Their covering families are the same as in `X`, so this is a sheaf and a functor
   (`def-weil-sheaf-of-modules-category`, `def-weil-pbc-module-finite-type-presentation`,
   `def-weil-pbc-sites-and-cohomology`).
2. Direct image evaluates on `V ∩ U`; coverings pull back to coverings, so it is a sheaf.
   Scalars act through the ring restriction to `V ∩ U`. Semilinearity follows by composing
   ring restrictions, and morphisms are evaluated on `V ∩ U`, giving a functor
   (`def-weil-pbc-topological-inverse-image`, `def-weil-sheaf-of-modules-category`).
3. Given `α`, the forward map on `V` restricts a section to `V ∩ U`, then applies `α` there.
   Semilinearity and linearity make this linear over the sections of the ring on `V`;
   naturality of `α` and composition of restrictions give compatibility with restrictions.
4. Given `β`, its components on opens contained in `U` define the inverse. The canonical
   identification of `U ∩ W` with `W` is the restriction along the unit of `forgetAdjStar`.
   This preserves the ring action and all restriction maps.
5. On an open contained in `U`, restricting to its intersection with `U` is the identity.
   Conversely, compatibility of `β` with restriction to `V ∩ U` shows that applying the
   forward map after the inverse recovers `β`. Thus the two maps are inverse bijections.
6. For `μ : M' ⟶ M` and `ν : G ⟶ G'`, both naturality composites on `V` send `s` to
   `ν (α (μ (s|_(V ∩ U))))`, since `μ` commutes with restrictions. These natural
   bijections constitute the asserted adjunction.
-/
theorem exists_openRestrictionAdjunction (X : RingedSpace.{u}) (U : Opens X) :
    ∃ adj :
      SheafOfModules.overFunctor.{w} (moduleRings X) U ⊣
        SheafOfModules.pushforward.{w}
          (SheafOfModules.pushforwardOver (R := moduleRings X) U),
      (∀ (M : SheafOfModules.{w} (moduleRings X))
        (G : SheafOfModules.{w} ((moduleRings X).over U))
        (α : M.over U ⟶ G) (V : Opens X) (s : M.val.obj (op V)),
        ((adj.homEquiv M G) α).val.app (op V) s =
          α.val.app (op ((Over.star U).obj V))
            (M.val.map (prod.snd : U ⨯ V ⟶ V).op s)) ∧
      (∀ (M : SheafOfModules.{w} (moduleRings X))
        (G : SheafOfModules.{w} ((moduleRings X).over U))
        (β : M ⟶ (SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj G)
        (W : Over U) (s : M.val.obj (op W.left)),
        ((adj.homEquiv M G).symm β).val.app (op W) s =
          G.val.map ((Over.forgetAdjStar U).unit.app W).op
            (β.val.app (op W.left) s)) := by
  sorry

end TopologicalSpace.Opens
