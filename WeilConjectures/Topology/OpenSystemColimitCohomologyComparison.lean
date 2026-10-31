/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.OpenSystemRestrictionPresentation
public import WeilConjectures.Topology.SpectralLimitCohomologyMap
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-! # Cohomology of the constant restriction system

Source: Stacks Project, Cohomology, Tags 0A3D and 0A37.
(blueprint: lem-weil-pbc-open-system-colimit-cohomology-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace TopCat.OpenSystem

variable {T I : Type u} [TopologicalSpace T] [Preorder I]
  [Nonempty I] [IsDirected I (· ≤ ·)]

attribute [local instance] IsFiltered.isConnected

/-- The colimit of the constant coefficients is the restriction to the common subspace.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-colimit-cohomology-comparison) -/
@[irreducible] def coefficientColimitIso (E : Set T)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
    colimit (coefficients (I := I) E A) ≅ (inverseImage (inclusion E)).obj A :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone I _)

/-- Cohomology of the canonical constant-colimit isomorphism.
Source: Stacks Project, Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-colimit-cohomology-comparison) -/
@[irreducible] def coefficientCohomologyColimitIso (E : Set T)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (q : ℕ) :
    CategoryTheory.Sheaf.H' (colimit (coefficients (I := I) E A)) q ⊤ ≅
      CategoryTheory.Sheaf.H' ((inverseImage (inclusion E)).obj A) q ⊤ :=
  ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology E) q).mapIso
      (coefficientColimitIso (I := I) E A)).app (op ⊤)

/-- Transport along the constant-system colimit comparison identifies the cohomology leg
with ordinary pullback followed by the inverse-image composition isomorphism.

Source: Stacks Project, Cohomology, Tags 01F7, 01F8 and 0A37, restriction-system setup.
(blueprint: lem-weil-pbc-open-system-colimit-cohomology-comparison)

Proof: The colimit coprojection followed by coefficientColimitIso is the identity.
Thus the adjoint of coefficientIso.inv followed by that coprojection, after mapping
by coefficientColimitIso, is the adjoint of restrictionIso.hom. Naturality of normalized
cohomology pullback in the coefficient sheaf moves the coefficientColimitIso cohomology
map across the pullback. Functoriality of the cohomology presheaf combines coefficient
maps and moves them across the final restriction from the inverse image of top to top.
The adjunction hom-bijection and the colimit coprojection identity give the displayed
equality. This argument uses neither spectrality nor a limit property of the spaces;
it is only functoriality in a coefficient isomorphism. -/
theorem coefficientColimit_cohomology_comparison
    (V : I → Opens T) (E : Set T) (hE : ∀ i, E ⊆ V i)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (i : I) :
    TopCat.Sheaf.spectralLimitCohomologyMap (inclusionOfLE (hE i))
        (objectCohomologyPullback (inclusionOfLE (hE i)))
        ((adjunction (inclusionOfLE (hE i))).homEquiv _ _
          ((coefficientIso V E hE A i).inv ≫ colimit.ι (coefficients E A) i)) q ≫
      (coefficientCohomologyColimitIso (I := I) E A q).hom =
    TopCat.Sheaf.spectralLimitCohomologyMap (inclusionOfLE (hE i))
      (objectCohomologyPullback (inclusionOfLE (hE i)))
      ((adjunction (inclusionOfLE (hE i))).homEquiv _ _
        (restrictionIso (hE i) A).hom) q := by sorry

end TopCat.OpenSystem
