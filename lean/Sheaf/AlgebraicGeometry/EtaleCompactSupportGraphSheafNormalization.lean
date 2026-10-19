/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# The graph map into the compactification sheaf

Source: Stacks Project Tag 0F4L (lemma-shriek-into-star-separated-etale),
and SGA 4 XVII 6.2.11 (blueprint: lem-asd-compact-support-graph-sheaf-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The graph transpose extends each sheet section by zero in the compactification.
Source: Stacks Project Tag 0F4L, lemma-shriek-into-star-separated-etale;
SGA 4 XVII 6.2.11.
(blueprint: lem-asd-compact-support-graph-sheaf-normalization).

Proof:
1. Transpose both sides under the sum-extension/restriction adjunction. A section over
an etale test object is thereby tested on each lift of that object to U.
2. The inverse beta in the graph projection identifies that lift with its base change
in Z times_X U. The composition comparison preserves the same left-adjoint units.
3. The projection to the graph is identity on the graph and zero on its complement:
its map into the graph direct image is the adjoint of the section identity, and the
clopen comparison between extension and direct image is inverted.
4. Inclusion of extension by zero into direct image keeps the underlying section.
Both transposes are therefore the graph-extension unit defining
etaleLowerShriekToLowerStar. Injectivity of the adjunction bijection proves equality.
Concretely, apply the injective homEquiv of etaleLowerShriekRestrictionAdjunction,
then lowerStarUnit_app_hom_app. Scheme.Etale.graph_hom_ext reduces the resulting
section equation to its graph and complement restrictions. The target restrictions
are graphExtend_graph and graphExtend_graphComplι. For the constructed transpose,
the inverse-conjugate counit equation for beta, the counit equation for leftAdjointUniq,
and the triangle identity for the clopen projection give respectively identity and zero.
The argument is valid for the empty graph, where all relevant sections are zero. -/
theorem compactSupportGraphSheafComparison_normalization
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X)
    [Etale f] [IsSeparated f] (c : Compactification f)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleCompactificationGraphMap A f c).app M ≫
        (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M := by
  sorry

end AlgebraicGeometry.Etale
