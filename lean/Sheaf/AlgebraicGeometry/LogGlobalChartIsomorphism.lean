/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Recognition of log isomorphisms from a common global chart

Source: ILO VI 1.1, p.69; Stacks Tags 03PQ and 03PU.
(blueprint: lem-trf-log-map-global-chart-isomorphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A structural log map which identifies two charts of the same monoid is an
isomorphism of monoid sheaves.

Source: ILO VI 1.1, p.69; Stacks Tags 03PQ, 03PU. This is only the
stalk-conservativity step of chart recognition; neither a map nor a chart is
constructed by this assertion.

Proof: at a geometric point take the induced colimit map on the monoid stalks.
It commutes with the structural maps, by naturality and the colimit equations.
It therefore carries the canonical inclusion of strict-local ring units into L
to that into K: apply the map on unit groups and use the injectivity of the
structural map on K's units. The equality on global charts becomes equality on
their germs. Both `IsChart` hypotheses identify the respective stalks with the
quotient of P times the same ring-unit group. Structural compatibility and the
chart equation identify their generating congruences. The induced stalk map is
therefore the map induced by the identity on pairs between two copies of the
same quotient. It is bijective, since each pair map is surjective and the two
kernels agree. Choose algebraic closures of residue fields. The associated
geometric points cover the scheme; conservativity of set stalks makes the
underlying sheaf map an isomorphism. The sectionwise inverse preserves one,
products and restrictions by injectivity. It hence gives the inverse morphism
of monoid sheaves. This also covers empty test schemes and the empty base.
(blueprint: lem-trf-log-map-global-chart-isomorphism). -/
theorem EtaleLogStructure.isIso_of_globalChart {X : Scheme.{u}}
    [IsLocallyNoetherian X] (L K : EtaleLogStructure.{u} X)
    {P : Type u} [CommMonoid P]
    (cL : P →* L.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (cK : P →* K.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hL : L.IsChart (Scheme.Etale.mk (𝟙 X)) cL)
    (hK : K.IsChart (Scheme.Etale.mk (𝟙 X)) cK)
    (f : L.monoidSheaf ⟶ K.monoidSheaf) (hf : f.hom ≫ K.alpha = L.alpha)
    (hc : (f.hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp cL = cK) :
    IsIso f := by
  sorry

end AlgebraicGeometry
