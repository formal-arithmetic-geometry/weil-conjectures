/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion

/-! # Acyclicity from surjective restrictions on quasi-compact opens

Source: Stacks Project, Cohomology of Sheaves, Tags 0A36 and 01EW, as used in
Tag 0A3G, proof of (1) from (2); Cohomology on Sites, Tag 03F9.
(blueprint: lem-sfb-quasi-compact-restriction-acyclicity)

The restriction in the conclusion is the ordinary restriction to the open subspace,
implemented by Mathlib's naive pullback along the open embedding. No compactness of
the ambient space, separation axiom, or Noetherian assumption is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

/-- Surjective restrictions between quasi-compact opens imply vanishing of positive
cohomology on every quasi-compact open subspace.

Source: Stacks Project, Cohomology of Sheaves, Tags 0A36 and 01EW, applied as in
Tag 0A3G, proof of (1) from (2); Cohomology on Sites, Tag 03F9.
(blueprint: lem-sfb-quasi-compact-restriction-acyclicity)

Proof:
1. Fix a quasi-compact open V and restrict G to V. The quasi-compact opens of X
   contained in V form a basis of V. Their finite covers, indexed by finite ordinals
   (including the empty ordinal), are cofinal among all covers of each basis open:
   refine pointwise by the basis and extract a finite subcover. This includes the
   empty open. Use the open site of def-weil-pbc-sites-and-cohomology.
2. By the intersection hypothesis every nonempty finite intersection in such a cover
   is quasi-compact. There are finitely many distinct intersections, so every union
   of these intersections is also quasi-compact, including the empty union. The
   restriction from the covered open to each such union is surjective by hres.
3. Apply lem-sfb-cech-vanishing-surjective-unions (Tag 0A36) to obtain positive
   ordered-tuple Cech vanishing for each finite cover. Tuples may have repetitions;
   their intersections are among the same finitely many intersections.
4. Apply lem-weil-pbc-site-cech-vanishing-criterion (Tag 03F9, the abelian-site form
   of 01EW): step 2 verifies intersection stability, step 1 gives cofinality, and
   step 3 gives Cech vanishing. Take the terminal open of V. By
   def-sc-topological-abelian-cohomology, its H' is the right-derived global sections
   of the ordinary restriction G|V. This gives the conclusion for every positive q
   and every quasi-compact V, including V empty. Compactness of X is never used.
-/
theorem subsingleton_H'_of_quasiCompact_restriction_surjective
    (X : Type u) [TopologicalSpace X]
    (hBasis : IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U})
    (hInter : ∀ (U V : Opens X), IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hres : ∀ (U V : Opens X) (hUV : U ≤ V),
      IsCompact (U : Set X) → IsCompact (V : Set X) →
      Function.Surjective (G.obj.map (homOfLE hUV).op))
    (V : Opens X) (hV : IsCompact (V : Set X)) (q : ℕ) (hq : 0 < q) :
    Subsingleton
      (@CategoryTheory.Sheaf.H'.{u, u, u}
        (Opens V) inferInstance (Opens.grothendieckTopology V) inferInstance
        (@hasExt_of_enoughInjectives _ _ _ inferInstance
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
              (Opens.grothendieckTopology V) AddCommGrpCat.{u})))
        ((Topology.IsOpenEmbedding.sheafPullback AddCommGrpCat.{u}
          (f := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          V.isOpenEmbedding').obj G) q ⊤) := by
  sorry

end TopCat.Sheaf
