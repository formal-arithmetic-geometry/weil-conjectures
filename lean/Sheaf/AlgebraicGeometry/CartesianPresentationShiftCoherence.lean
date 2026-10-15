/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.RawRestrictedDerivedComparisonPullback
public import Sheaf.AlgebraicGeometry.RestrictedDerivedSectionPullbackCommShift
import all Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport

/-! # Shift coherence for a cartesian presentation

Source: Stacks Project, Tags 07A6, 0D6F, and 0GIT.
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option maxRecDepth 2048

/-- The degree-`q` restricted cohomology map is the homology of the unshifted
derived section map, for any bounded-below coefficient. The derived unit,
Leray comparison, inverse-image comparison, and coefficient map commute with
shifts. Apply the generic `transport_homology` square to those four maps, then
cancel the source shift isomorphism. No single-sheaf hypothesis is used. -/
theorem cartesianPresentation_shiftCoherence {C C' D E : Type u}
    [Category C] [Category C'] [Category D] [Category E]
    [HasShift C ℤ] [HasShift C' ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (T : C ⥤ D) (T' : C' ⥤ D) (L : C ⥤ C')
    [T.CommShift ℤ] [T'.CommShift ℤ] [L.CommShift ℤ]
    (τ : T ⟶ L ⋙ T') [NatTrans.CommShift τ ℤ]
    (H₀ : D ⥤ E) (Hq : D ⥤ E) (q : ℤ)
    (σ : shiftFunctor D q ⋙ H₀ ⟶ Hq)
    {K : C} {K' : C'} (φ : L.obj K ⟶ K') :
    H₀.map (τ.app (K⟦q⟧)) ≫
        H₀.map (T'.map ((L.commShiftIso q).hom.app K ≫
          (shiftFunctor _ q).map φ)) ≫
        H₀.map ((T'.commShiftIso q).hom.app K') ≫ σ.app (T'.obj K') =
      H₀.map ((T.commShiftIso q).hom.app K) ≫ σ.app (T.obj K) ≫
        Hq.map (τ.app K ≫ T'.map φ) := by
  have hs := RawRestrictedComparison.transport_homology
    T T' L τ H₀ Hq q σ φ (Iso.refl (T.obj K)) (Iso.refl (T'.obj K'))
  simpa only [Iso.refl_hom, Iso.refl_inv, Hq.map_id, Category.id_comp,
    Category.comp_id, ← Functor.map_comp, Category.assoc] using hs

end AlgebraicGeometry.Etale
