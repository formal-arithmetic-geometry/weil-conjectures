/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.Sheaves.Stalks

/-!
# Extending sections along closed subsets to neighborhoods

Source: Demailly, Complex Analytic and Differential Geometry, IV §4.B,
Lemma (4.6)(a), Theorem (4.7), Corollary (4.8), printed pp.203–204
(blueprint: lem-sfb-closed-section-neighborhood-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- A section of an abelian sheaf along a closed subset of a paracompact Hausdorff
space extends to an open neighborhood. The inverse image is Mathlib's sheaf pullback
along the subspace inclusion. Restriction is its adjunction unit on `U`, followed by
restriction from the inverse image of `U` to the top open of the subspace.

Source: Demailly, Complex Analytic and Differential Geometry, IV §4.B,
Lemma (4.6)(a), Theorem (4.7), Corollary (4.8), printed pp.203–204
(blueprint: lem-sfb-closed-section-neighborhood-extension).

Proof:
1. If S is empty, take U = X and t = 0. Otherwise represent the section locally
   along S by sections s_a on open neighborhoods U_a. Equality of germs means
   equality after restriction to a smaller common open neighborhood.
2. Apply lem-sfb-paracompact-closed-cover-refinement (`precise_refinement_set`)
   to obtain a locally finite open cover W_a of S with W_a contained in U_a.
3. This cover is point-finite on S. Apply lem-sfb-paracompact-point-finite-shrinking
   (`exists_subset_iUnion_closure_subset`) to obtain open V_a covering S with
   closure V_a contained in W_a. The family V_a remains locally finite in X.
4. Inside the union of V_a, let E consist of points where the germs of s_a and s_b
   agree whenever the point lies in both closures. The germs are defined by the
   closure containment, and E contains S because each representative gives s there.
5. To show E open, choose a neighborhood meeting only finitely many V_a. It also
   misses all other closures. Remove the finitely many remaining closures not
   containing the chosen point. For each pair of closures through the point,
   intersect with a neighborhood on which their representatives agree. This finite
   intersection, further intersected with the union of V_a, is contained in E.
6. Restrict s_a to E intersect V_a. They agree on overlaps by
   lem-weil-pbc-sheaf-sections-determined-by-germs (`TopCat.Presheaf.section_ext`).
   The sheaf equalizer axiom of def-weil-pbc-sites-and-cohomology glues them to t
   on E. Its germs along S are s, so its inverse-image restriction equals s.
-/
theorem exists_neighborhood_extension_of_isClosed
    {X : TopCat.{u}} [ParacompactSpace X] [T2Space X]
    (G : X.Sheaf AddCommGrpCat.{u}) (S : Set X) (hS : IsClosed S)
    (s : ((pullback AddCommGrpCat.{u}
      (TopCat.ofHom ⟨(Subtype.val : S → X), continuous_subtype_val⟩)).obj G).obj.obj
        (op (⊤ : Opens S))) :
    ∃ (U : Opens X) (hSU : S ⊆ (U : Set X)) (t : G.obj.obj (op U)),
      ((pullback AddCommGrpCat.{u}
        (TopCat.ofHom ⟨(Subtype.val : S → X), continuous_subtype_val⟩)).obj G).obj.map
          (homOfLE (fun (x : S) (_ : x ∈ (⊤ : Opens S)) ↦ hSU x.property)).op
            ((((pullbackPushforwardAdjunction AddCommGrpCat.{u}
              (TopCat.ofHom ⟨(Subtype.val : S → X), continuous_subtype_val⟩)).unit.app G).hom.app
                (op U)) t) = s := by
  sorry

end TopCat.Sheaf
