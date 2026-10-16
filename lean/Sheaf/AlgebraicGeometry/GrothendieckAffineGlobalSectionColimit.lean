/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import Sheaf.Paper.EtaleFiniteDataDescent

/-! # Global-section continuity for inverse systems of affine schemes -/

@[expose] public section

universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Global sections of a fixed sheaf pulled back to affine schemes commute with directed inverse
limits over a fixed affine base. The supplied diagram and cocone are normalized by the displayed
unit/composition equations; no objects are chosen from an existence assertion. Source: Stacks
Project, Etale Cohomology, Tag 09YQ, degree zero; Sites, Tag 0738(4); blueprint
etale-cohomology-continuity, detailed proof, paragraph 2.

Proof: work on the affine etale bases over the fixed affine base and its stages. Finite-presentation
etale affine objects over the limit descend to stages, as do their morphisms, equalities and finite
covering families. Any two models acquire a common later model, and any two comparison arrows become
equal at a later stage. For a limit affine object V, use the filtered category of its stage models
and let Q(V) be the colimit in A of the sections of the corresponding stage pullbacks of G. Lift a
restriction arrow to a common stage; the colimit universal property and eventual equality make the
result independent of the lift, and give identity and composition. For a fixed model, its later base
changes are cofinal among all models, by descent of comparison maps and eventual equality. Thus
these colimits may be computed on u-small upper tails.

A finite affine etale covering of V, its pairwise pullbacks, and all matching maps descend
simultaneously, and the family is covering at every sufficiently late stage. The stage sheaf
conditions are finite matching limits. AB5, after shrinking the filtered-colimit universe from u+1
to u, preserves those limits; hence Q satisfies the sheaf condition on the affine etale basis. This
includes the empty cover and zero coefficient objects. The affine basis comparison extends Q to a
sheaf on the small etale site of the limit. Write p_j for the projection from the limit to stage j.
A map from Q to any sheaf M is exactly a compatible family of maps from pi_j^* G to (p_j)_* M.
The stage adjunctions identify each such Hom set with Hom(G, (pi_j)_* (p_j)_* M).
Composition of direct images identifies these, compatibly, with the constant set Hom(G, p_* M).
Directedness and nonemptiness identify that family with a single map from G to the direct image of M
on the fixed base. Identity presentations and the units give the two inverse assignments. Thus Q is
the inverse image of G, compatibly with the units. Evaluation at the terminal affine object gives
the asserted section colimit. Inverse-image composition coherence identifies its legs and
transitions with hK and hH; transport along e and eK gives the universal property for the supplied
K. No elementwise finite factorization of maps from arbitrary objects of A is asserted or used.
(blueprint: lem-weil-pbc-grothendieck-affine-global-section-colimit) -/
theorem affine_globalSections_limit_isColimit_of_directed
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J] {S : Scheme.{u}}
    [IsAffine S]
    (D : Jᵒᵖ ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (π : D ⟶ (Functor.const Jᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ j : J, p = c.π.app (op j) ≫ π.app (op j))
    (G : Sheaf S.smallEtaleTopology A) (H : J ⥤ A)
    (e : ∀ j : J, H.obj j ≅ (Sheaf.Γ (D.obj (op j)).smallEtaleTopology A).obj
      ((upperStar A (π.app (op j))).obj G))
    (hH : ∀ (j k : J) (f : j ⟶ k), H.map f ≫ (e k).hom =
      (e j).hom ≫ globalSectionsUpperStarMap A (D.map f.op)
        ((upperStar A (π.app (op j))).obj G) ≫
      (Sheaf.Γ (D.obj (op k)).smallEtaleTopology A).map
        ((upperStarComp A (D.map f.op) (π.app (op j)) (π.app (op k))
          (by simpa only [Functor.const_obj_obj, Functor.const_obj_map,
            Category.comp_id] using (π.naturality f.op).symm)).inv.app G))
    (K : Cocone H) (eK : K.pt ≅ (Sheaf.Γ c.pt.smallEtaleTopology A).obj
      ((upperStar A p).obj G))
    (hK : ∀ j : J, K.ι.app j ≫ eK.hom =
      (e j).hom ≫ globalSectionsUpperStarMap A (c.π.app (op j))
        ((upperStar A (π.app (op j))).obj G) ≫
      (Sheaf.Γ c.pt.smallEtaleTopology A).map
        ((upperStarComp A (c.π.app (op j)) (π.app (op j)) p (hp j)).inv.app G)) :
    Nonempty (IsColimit K) := by sorry

end AlgebraicGeometry.Etale
