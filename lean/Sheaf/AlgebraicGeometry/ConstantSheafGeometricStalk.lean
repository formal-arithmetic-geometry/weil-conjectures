/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!
# The canonical map to the geometric stalk of a constant étale sheaf

Source: Stacks Project, Étale Cohomology, Tags 03PT (2), 040R and 03PQ
(blueprint: lem-weil-pbc-constant-sheaf-geometric-stalk).
-/

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The global constant section followed by its germ is an isomorphism of abelian groups.
Source: Stacks Project, Tags 03PT (2), 040R and 03PQ
(blueprint: lem-weil-pbc-constant-sheaf-geometric-stalk).

Proof:
1. The stalk of the constant sheaf is the stalk of its constant presheaf, via the map
   induced by sheafification (lem-weil-pbc-sheafification-geometric-stalk, Tag 03PT (2)).
2. Pointed étale neighbourhoods are cofiltered and contain the identity neighbourhood
   (lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered, Tag 03PQ). Their opposite category
   is nonempty and connected. The stalk of the constant presheaf is the colimit of the
   constant diagram with identity transition maps; every coprojection is an isomorphism
   (lem-weil-pbc-colimit-constant-connected-diagram). In particular the coprojection at
   the identity neighbourhood sends an element to its constant-presheaf germ.
3. Naturality of the stalk coprojections identifies the composite of these two
   isomorphisms with the map displayed below: an element goes to the germ of its global
   constant section (def-weil-pbc-geometric-stalks, Tag 040R).

The pointed neighbourhood is explicitly `(T, t)`: `Etale.mk (𝟙 T)` with lift `t`, and the
stalk is that of the point `pointSmallEtale t` (its `sheafFiber` on sheaves). -/
theorem constantSheaf_geometricStalk_isIso (T : Scheme.{u})
    (E : AddCommGrpCat.{(max u v) + 1}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    IsIso ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj E)).app
      (op (Etale.mk (𝟙 T))) ≫
        (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
          (Over.homMk t (Category.comp_id t))
          ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{(max u v) + 1}).obj E).obj) := by
  sorry

end AlgebraicGeometry.Scheme
