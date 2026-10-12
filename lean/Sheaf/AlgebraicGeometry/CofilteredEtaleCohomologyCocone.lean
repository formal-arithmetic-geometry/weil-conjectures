/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# A cohomology colimit cocone for a cofiltered system over a fixed scheme

Source: Stacks Project, Theorem 59.51.3, Tag 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The canonical cohomology diagram of the restrictions of an abelian sheaf to a
cofiltered qcqs system with affine transitions has a colimit given by limit cohomology.
The stage isomorphisms identify its objects, and `r` records the compatible restriction
maps from the fixed base. The last equation specifies the comparison on those maps.

Source: Stacks Project, Theorem 59.51.3 (Tag 09YQ), with the cofiltered-category reduction
of `lem-weil-pbc-filtered-category-exists-directed-final`.
(blueprint: lem-weil-pbc-cofiltered-etale-cohomology-cocone)

Proof:
1. At stage j take the abelian group H^q(D_j, pi_j inverse image of G). Along an
   arrow k to j use cohomological pullback followed by the inverse-image composition
   isomorphism. Naturality of pi and inverse-image coherence give identity and
   composition, defining H on J opposite. The maps r_j are cohomologyMap pi_j.
   Pullback functoriality proves their displayed compatibility.
2. The composites c_j followed by pi_j agree: choose a common predecessor for any
   two indices, and use the cone and natural transformation equations. Call this
   map t. Inverse-image composition identifies the pullback to the limit of every
   stage sheaf with t inverse image of G, compatibly with all transitions.
3. Choose a small directed final functor to J opposite. Its opposite is initial,
   so the reindexed scheme cone is still a limit and has the same limit object.
   The constant compatible limit sheaves have colimit t inverse image of G,
   since the index category is nonempty and connected.
4. Apply Tag 09YQ to the reindexed directed qcqs system with affine transitions.
   It identifies the colimit of its cohomology groups with H^q(c.pt, t inverse
   image of G). Finality transfers this colimit universal property to J opposite.
   Use the canonical pullback maps to form B; the comparison is an isomorphism e.
5. Pullback functoriality and the composition comparisons identify e B_j r_j
   with cohomologyMap t. The stage identifications give eH_j r_j = cohomologyMap
   pi_j. These prove all displayed equations. No torsion assumption is used.

This asserts a cohomology colimit, before choosing a class or testing vanishing.
It includes q = 0, zero sheaves, empty schemes and a one-object index category. -/
theorem exists_cofiltered_etale_cohomology_cocone
    {J : Type u} [SmallCategory J] [IsCofiltered J] {S : Scheme.{u}}
    (D : J ⥤ Scheme.{u}) (π : D ⟶ (Functor.const J).obj S)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (j₀ : J) :
    ∃ (H : Jᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (eH : ∀ j : J, H.obj (op j) ≅
        AddCommGrpCat.of (Sheaf.H (((π.app j)^*[AddCommGrpCat.{u + 1}]).obj G) q))
      (r : ∀ j : J, Sheaf.H G q →+ H.obj (op j)),
      (∀ (j k : J) (f : j ⟶ k) (x : Sheaf.H G q),
        H.map f.op (r k x) = r j x) ∧
      (∀ (j : J) (x : Sheaf.H G q), (eH j).hom (r j x) = cohomologyMap (π.app j) G q x) ∧
      ∃ (B : Cocone H) (_ : IsColimit B)
        (e : B.pt ≅ AddCommGrpCat.of
          (Sheaf.H (((c.π.app j₀ ≫ π.app j₀)^*[AddCommGrpCat.{u + 1}]).obj G) q)),
        ∀ (j : J) (x : Sheaf.H G q),
          e.hom (B.ι.app (op j) (r j x)) =
            cohomologyMap (c.π.app j₀ ≫ π.app j₀) G q x := by sorry

end AlgebraicGeometry.Etale
