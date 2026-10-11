import Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Positive-degree Zariski cohomology classes vanish locally

Source: Stacks Project, Etale Cohomology, Lemma 0GY0 (label `lemma-gabber-criterion`),
line 14228, proof (blueprint: lem-weil-pbc-zariski-cohomology-locally-zero).
-/

universe u v

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option synthInstance.maxHeartbeats 2000000 in
-- Cohomology uses the Ext localization instance for Zariski sheaves.
/-- Positive-degree cohomology classes on a scheme are locally zero.

Source: Stacks Project, Etale Cohomology, Lemma 0GY0 (label `lemma-gabber-criterion`),
line 14228, proof; Cohomology on Sites, Lemma 01FW.  The cohomology groups and their
restriction maps are rendered by Mathlib's cohomology presheaf; an injective resolution
is included as the resolution used to compute the groups.
The assertion is the four-step proof in the node
(blueprint: lem-weil-pbc-zariski-cohomology-locally-zero).
-/
theorem zariski_cohomology_class_locally_zero {X : Scheme.{u}}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (I : InjectiveResolution G) (q : ℕ) (hq : 0 < q)
    (ξ : (G.cohomologyPresheaf q).obj (op ⊤)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ((G.cohomologyPresheaf q).map
        (homOfLE (X := X.Opens) (x := U) (y := ⊤) le_top).op).hom ξ = 0 := by
  sorry

end AlgebraicGeometry
