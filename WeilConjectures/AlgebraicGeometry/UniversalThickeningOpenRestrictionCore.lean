/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenPieces

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The open restriction data for a universal first order thickening exists: for opens
`V ≤ h ⁻¹ᵁ U`, there is an open `V'` of `Z'` with `i ⁻¹ᵁ V' = V` such that the restricted
thickening `V ⟶ V'` is universal over `U`.
Source: Stacks Project, More on Morphisms, Lemma 04FA and Lemma 04F3. -/
theorem universalFirstOrderThickening_open_restriction_core
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : IsUniversalFirstOrderThickening h i h')
    (V : Z.Opens) (U : X.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    ∃ (hV : V.toScheme ⟶ U.toScheme),
      V.ι ≫ h = hV ≫ U.ι ∧ ∃ (V' : Z'.Opens) (iV : V.toScheme ⟶ V'.toScheme)
          (hV' : V'.toScheme ⟶ U.toScheme),
          i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
          iV ≫ V'.ι = V.ι ≫ i ∧ hV' ≫ U.ι = V'.ι ≫ h' ∧
          iV ≫ hV' = hV ∧ IsUniversalFirstOrderThickening hV iV hV' := by
  obtain ⟨V', hiV', hV'U, iV, hV, hV', hiV, hhV, hhV', HV⟩ :=
    (universalFirstOrderThickening_open_pieces h).2.1 i h' H V U hVU
  exact ⟨hV, hhV.symm, V', iV, hV', hiV', hV'U, hiV, hhV', HV.2.1, HV⟩

end AlgebraicGeometry
