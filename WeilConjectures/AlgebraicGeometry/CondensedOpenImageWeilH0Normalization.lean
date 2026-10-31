/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs

/-! Degree-zero normalization of the canonical condensed derived Weil map. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The degree-zero derived Weil map is the ordinary coefficient mate, under the
canonical left-exact H0 identification.
Source: latest blueprint, p-dl-a1-exact, Step 1, degree-zero identification
(blueprint: new-dl-a1-weil-h0-normalization).
Proof: characterize the canonical H0 comparison by the single-derived unit.
The exchange is a right mate, so its unit square is the image of the canonical
pullback-composition comparison. Restrict this square to a single object and take
H0. Exact pullback and its single comparison identify its top and bottom maps
with the underived pullback square. The unit characterization of ordinary base
change therefore identifies the resulting map with lowerStarBaseChange.
Finally use naturality of singleRightDerivedH0Iso for the coefficient map φ.hom.
This argument concerns one object and does not use a short exact sequence. -/
theorem condensedOpenImage_weil_h0_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} {gU : U ⟶ U} {gC : C ⟶ C}
    (j : U ⟶ C) (sq : CommSq gU j j gC)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (φ : (upperStar Λ gU).obj M ≅ M) :
    (upperStar Λ gC).map ((lowerStar Λ j).singleRightDerivedH0Iso M).inv ≫
        dlOpenImageHomologyWeilMap Λ j sq M φ 0 =
      dlOpenImageWeilMap Λ j sq M φ ≫ ((lowerStar Λ j).singleRightDerivedH0Iso M).inv := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
