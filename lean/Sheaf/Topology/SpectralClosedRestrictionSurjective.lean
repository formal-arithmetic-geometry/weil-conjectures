/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Sheaves.Functors
import Sheaf.Topology.ClosedPushforwardConstantRestriction
import Sheaf.Topology.SheavesDirectedColimitSections
import Sheaf.Topology.SpectralClosedClopenDecompositionLift
import Sheaf.Topology.SpectralClosedSubspace
import Sheaf.Topology.SpectralSheafColimitConstantEmbeddings

/-! # Surjectivity of spectral closed restriction, Stacks Tag 09ZG -/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Etale Cohomology, Lemma 59.82.1 (Tag 09ZG),
its finite constant-sheaf, subsheaf and filtered-colimit arguments.
(blueprint: lem-weil-pbc-h0-spectral-closed-restriction-surjective)

Proof:
1. Restriction of locally constant maps with finite values is surjective. Split
   the closed subset by one value of the map. The clopen-decomposition lifting
   lemma lifts this split to the spectral ambient space. Induction on the finite
   number of values gives the extension on each piece, which glues since the
   pieces are open. The empty-value case forces the ambient space to be empty.
2. A finite product of finite constant sheaves pushed forward from closed subsets
   also has surjective restriction. Inverse image preserves finite products.
   For a factor, closed-pushforward restriction identifies the restricted sections
   with locally constant maps on the intersection of the two closed subsets.
   Closed subspaces are spectral, and the connectedness hypothesis is inherited
   because the closure of a point in a closed subspace equals its ambient closure.
   Apply step 1 in each closed subspace and take the product of the lifts.
3. If a sheaf embeds sectionwise into such a product, lift the image of the given
   restricted section to a global product section. At each point of the closed
   subset, the inverse-image stalk comparison gives a local preimage in the
   subsheaf. Equality of germs shrinks the neighbourhood so this preimage maps
   to the chosen product section. Each ambient point specializes to a point of
   the closed subset, so these neighbourhoods cover the ambient space. The local
   preimages agree on overlaps by sectionwise injectivity, hence glue. Inverse
   image preserves this injectivity on stalks and therefore on sections, so the
   glued section restricts to the prescribed section.
4. Present the arbitrary sheaf as the directed colimit of sheaves embedding in
   the finite products of step 2. Inverse image preserves this colimit. The
   closed subset is spectral; its global sections commute with directed colimits
   since finite coverings by compact opens with compact intersections are cofinal.
   Thus the given section comes from one term. Step 3 lifts it globally in that
   term. Apply its cocone map; naturality of the adjunction unit shows that this
   image has the required restriction. -/
theorem spectral_closed_restriction_surjective
    (X : TopCat.{u}) [SpectralSpace X]
    (Z : Set X) (hZ : IsClosed Z)
    (hconn : ∀ x : X, ConnectedSpace (↥(Z ∩ closure ({x} : Set X))))
    (F : X.Sheaf (Type u)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let R := (Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F
    Function.Surjective
      (fun s : F.1.obj (op ⊤) =>
        (R.1.app (op ⊤)) s) := by
  sorry

end TopCat
