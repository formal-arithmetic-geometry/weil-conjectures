/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Mathlib.CategoryTheory.Filtered.Basic
import Sheaf.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections
import Sheaf.AlgebraicGeometry.EtaleInverseImageColimits
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-!
# Higher direct images and filtered diagrams at coefficient size

Source: Stacks Project, Tags 0739 and 03Q8, and the proof of Tag 09Z1.
(blueprint: lem-sbc-higher-direct-image-large-filtered-colimit)
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Higher direct image along a qcqs morphism preserves filtered diagrams indexed
in the coefficient universe, without a torsion assumption.

Source: Stacks Project, Tag 0739 (lemma-colim-works-over-collection),
Tag 03Q8 (higher-image cohomology presheaf), and Tag 09Z1 (lemma-relative-colimit).
(blueprint: lem-sbc-higher-direct-image-large-filtered-colimit)

Proof:
1. For an affine etale object W of X, its pullback Z to Y is qcqs. Restriction to Z
preserves colimits because it is a left adjoint. For q >= 0, apply
Scheme.etaleCohomology_isColimit_large_filtered on Z, then the natural comparison
Scheme.nonempty_etaleModuleCohomology_forgetIso and reflection of colimits by the
coefficient forgetful functor. This gives module cohomology continuity at size u+1.
The free-sheaf derived-sections comparison identifies the cohomology functor with
maps from the degree-zero free sheaf on Z into a shifted degree-zero sheaf.
2. Higher direct image is locally identified with this cohomology presheaf, by
isLocallyBijective_higherDirectImagePresheafToSheaf. Compute the colimit of the
higher images by sheafifying their presheaf colimit, and compare its vertex with
the higher image of the input colimit using its universal property.
3. The comparison is locally surjective: lift a higher-image section locally to
its cohomology presheaf, refine by affine etale objects, and use continuity from
step 1 to represent the class at a stage. Its image gives the required local lift.
4. It is locally injective: represent a section of the sheafified colimit locally
at a stage and lift that representative to a cohomology class. If its comparison
image is zero, local injectivity of the presheaf comparison makes that class zero
locally in the input colimit. Refine by affine objects. Continuity from step 1 and
exactness of filtered abelian-group colimits make its class zero at a later stage.
The original section therefore vanishes locally. Local bijectivity makes the
comparison an isomorphism, which is precisely colimit preservation.
5. For q < 0, degree-zero sheaves and their derived pushforwards are nonnegative;
t-structure orthogonality gives zero cohomology, so the functor is zero and
preserves colimits. The argument uses finite covers and finitely many matching
equalities only. It does not shrink J to Type 0. It includes the zero ring, empty
schemes, degree zero, and singleton indexing categories. -/
theorem preservesColimitsOfShape_higherDirectImage_large
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) := by sorry

end AlgebraicGeometry.Etale
