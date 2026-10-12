/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteSplitEtaleHypercover
public import Sheaf.Paper.EtaleHypercover
import Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting
import Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember

/-! Intermediate construction for finite split hypercover refinement. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Source: Stacks Project, Hypercoverings, Tags 0DAV, 094K, 01GS.

Proof: In degree n represent maps from the finite simplicial set Delta[1] times Delta[n]
to V by the finite limit of V's terms indexed by its nondegenerate simplices and face
relations. These limits exist in the etale site and remain limits after forgetting to
schemes over X. Restriction along simplicial operators defines the endpoint path object
of V. Pull its endpoint map back along (a,b) from U.
Its projection c to U carries the universal simplicial homotopy between c followed by a and c
followed by b. To verify the hypercover condition, the relative matching maps are restrictions from
the whole prism to
the endpoint simplices together with its boundary. The inclusion adds finitely many
nondegenerate simplices. Finite simplex lifting makes these restrictions covering; base change
preserves the covers. The singleton matching comparison identifies this covering condition with
the scheme matching condition. In degree zero the relative arrow is a pullback of
V_1 to V_0 times_X V_0. In each higher degree compose the relative covering arrow with
the base change of U's matching cover to obtain K's absolute matching cover. The resulting K need
not be finite or split; finite replacement
is a separate step.
(blueprint: lem-weil-pbc-etale-hypercover-homotopy-equalizer) -/
theorem exists_etale_hypercover_homotopy_equalizer
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : FiniteSplitEtaleHypercover X) (a b : U.Refinement V) :
    ∃ (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K)
      (c : K ⟶ U.simplicial), Nonempty (SimplicialObject.Homotopy (c ≫ a) (c ≫ b)) := by
  sorry

end AlgebraicGeometry.FiniteSplitEtaleHypercover
