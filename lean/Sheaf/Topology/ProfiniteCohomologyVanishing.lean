/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Topology.Sheaves.LocallySurjective
import Sheaf.Topology.PresheafModuleStalkFunctor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ExactSequence
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Abelian sheaf cohomology on a profinite topological space

Source: Stacks Project, Cohomology of Sheaves, Tag 0A3F,
`lemma-vanishing-for-profinite`
(blueprint: lem-cbc-profinite-topological-cohomology-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

/-- Every abelian sheaf on a compact Hausdorff totally disconnected space has zero
cohomology in positive degree. The cohomology is the recorded `Sheaf.H'` at the top open.

Source: Stacks Project, Cohomology of Sheaves, Tag 0A3F
(blueprint: lem-cbc-profinite-topological-cohomology-vanishing).

Proof:
1. For an epimorphism F → E and e ∈ E(X), use
   lem-sc-abelian-sheaf-epi-iff-stalk-epi to lift each germ e_x. Represent the lift by
   a section and shrink its neighbourhood until its image equals e there, using the
   germ representation and equality criterion of def-weil-pbc-module-stalk.
2. By lem-weil-pbc-profinite-clopen-basis, refine these neighbourhoods by clopens.
   Compactness gives a finite subcover C₁, ..., Cₙ. Subtract the preceding clopens
   from each Cᵢ to obtain a disjoint finite clopen refinement. For empty X use the
   empty cover; empty parts can always be discarded.
3. Restrict the lifts to the disjoint parts and glue by the sheaf axiom of
   def-weil-pbc-sites-and-cohomology. Sections agree on empty intersections because
   F(∅) = 0. Their glued image equals e by uniqueness. Thus global sections carry
   epimorphisms to surjections and, being additive and left exact, are exact.
4. By lem-weil-pbc-site-sheaves-enough-injectives, embed any G in an injective I
   and take its cokernel Q. The abelian-category kernel/cokernel property of
   def-sp-abelian gives a short exact sequence in the sense of
   def-weil-pbc-exact-sequence. Cohomology of I vanishes in positive degree and
   degree zero is global sections by def-weil-pbc-sites-and-cohomology.
5. Apply lem-weil-pbc-right-derived-universal-delta-functor. In the long exact
   sequence I(X) → Q(X) → H¹(X,G) → H¹(X,I), the first arrow is surjective by
   step 3 and the last term is zero by step 4. Hence H¹(X,G) = 0 for every G.
6. Induct simultaneously for all sheaves: the long exact sequence identifies
   Hʳ⁺¹(X,G) with Hʳ(X,Q) for r > 0, as the adjacent cohomology groups of I
   vanish. The induction hypothesis kills Hʳ(X,Q). This is exactly the cohomology
   of def-sc-topological-abelian-cohomology.
-/
theorem subsingleton_H'_top_of_profinite
    (X : TopCat.{u}) [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : 0 < q) :
    Subsingleton
      (@CategoryTheory.Sheaf.H'.{u, u, u}
        (Opens X) inferInstance (Opens.grothendieckTopology X) inferInstance
        (@hasExt_of_enoughInjectives _ _ _ inferInstance
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
              (Opens.grothendieckTopology X) AddCommGrpCat.{u}))) G q ⊤) := by
  sorry

end TopCat.Sheaf
