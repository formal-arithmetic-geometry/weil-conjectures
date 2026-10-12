/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectGluingEndpointProperties

/-! # Small classes of restrictions of perfect objects

Source: Step 2 of lem-pc-perfect-complexes-compact-set; Stacks Project, Tag 08DR
(blueprint: lem-perfect-restriction-classes-small).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Smallness on an open bounds the restriction classes of perfect objects on a larger open.
Source: Step 2 of lem-pc-perfect-complexes-compact-set; Stacks Project, Tag 08DR
(blueprint: lem-perfect-restriction-classes-small).

Proof: The composite j : (f⁻¹W).toScheme → Y → X is an open immersion.
Its image is f.opensRange ∩ W = W, using hW. Module sheaves on (f⁻¹W).toScheme
are equivalent to module sheaves on the localized site of Y at f⁻¹W, via
Modules.overEquiv. Transport the given derived category across this abelian
equivalence: first use a standard localization on the open scheme, whose derived
category is equivalent to the given localization of the localized module category.
It is locally w-small, so hasLocalizationOfLocallySmall provides a localization
in universe w. For each open of (f⁻¹W).toScheme, its image in Y lies below f⁻¹W;
the over-site equivalence and the equivalence between successive over sites and
the single over site at this image transport the given local structures the same way.
Apply pW to j with these structures to get a u-small perfect quasi-coherent skeleton.
For a perfect quasi-coherent E on Y, exact restriction commutes with homology and
preserves quasi-coherence. Its restriction is perfect: intersect its strictly perfect
neighbourhoods with f⁻¹W, use the iterated restriction isomorphism, and restrict the
bounded finite-free retract data. Transport to the open scheme. Thus its restriction
belongs to that perfect quasi-coherent subcategory. Choose the skeleton representative
of each such restriction and transport it back via the derived over-site equivalence.
The inclusion of the restriction family into the ambient localized derived category
is fully faithful. Its induced map on skeletons is injective, with image contained in
the range of the map from the small perfect skeleton on the open scheme. Therefore
small_of_injective applied into that small range proves the assertion. This concerns
only restrictions, without direct images or triangles. Empty W gives the zero class;
W = f.opensRange is the identity restriction case. -/
theorem perfectRestriction_classes_small (X : Scheme.{u}) (W : X.Opens)
    (pW : PerfectComplexClassesSmallOnOpen.{u, w} X W)
    (Y : Scheme.{u}) (f : Y ⟶ X) [IsOpenImmersion f] (hW : W ≤ f.opensRange)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ A : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over A))] :
    Small.{u} (Skeleton (perfectGluingRestrictionProperty Y (f ⁻¹ᵁ W)).FullSubcategory) := by
  sorry

end AlgebraicGeometry.Scheme
