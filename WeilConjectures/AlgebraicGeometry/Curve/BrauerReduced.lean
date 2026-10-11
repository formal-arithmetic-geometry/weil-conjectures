/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Brauer
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.GaGmLowerStar
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# The Brauer group of a reduced curve

The Brauer group `H²(C_ét, 𝔾ₘ)` of a reduced curve `C` over an algebraically closed field
vanishes. Let `Zₚ` be the irreducible components of `C` with their reduced structure and
`νₚ : Yₚ ⟶ C` their normalizations (or the point `Zₚ` itself if `Zₚ` is a point). The map
`𝔾ₘ ⟶ ⨁ₚ νₚ_* 𝔾ₘ` is an isomorphism away from the finitely many closed points where two components
meet or where some `Yₚ ⟶ Zₚ` is not an isomorphism, hence bijective on `H²`; and
`H²(C, νₚ_* 𝔾ₘ) = H²(Yₚ, 𝔾ₘ)` vanishes since `Yₚ` is a smooth curve or a point.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_isReduced`: the Brauer
  group of a reduced curve over an algebraically closed field vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

open Etale

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **One component of a reduced curve.** Let `Z` be an integral curve over an algebraically
closed field `k`. There is a finite morphism `n : Y ⟶ Z`, an isomorphism over a nonempty open
`W ⊆ Z`, with `Br(Y) = 0`: the normalization if `Z` has dimension one (a smooth curve), and the
spectrum of the residue field if `Z` is a point. -/
lemma exists_isFinite_isIso_subsingleton_cohomologicalBrauerGroup {Z : Scheme.{u}}
    [IsIntegral Z] (g : Z ⟶ Spec (.of k)) [IsCurve g] :
    ∃ (Y : Scheme.{u}) (n : Y ⟶ Z) (_ : IsFinite n) (W : Z.Opens), (W : Set Z).Nonempty ∧
      IsIso (n ∣_ W) ∧ Subsingleton Y.CohomologicalBrauerGroup := by
  sorry

/-- **The Brauer group of a reduced curve vanishes.** For a reduced curve `C` over an
algebraically closed field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. Let `νₚ : Yₚ ⟶ C` be the
normalizations of the irreducible components `Zₚ` of `C` (with their reduced structure). The map
`𝔾ₘ ⟶ ⨁ₚ νₚ_* 𝔾ₘ` is an isomorphism away from a finite set of closed points
(`AlgebraicGeometry.Scheme.isIso_upperStar_map_gmSheafToLowerStarGmSheaf`), hence bijective on
`H²` (`AlgebraicGeometry.Etale.bijective_H_map_of_isIso_upperStar_map`), and
`H²(C, νₚ_* 𝔾ₘ) = Br(Yₚ) = 0`.
(blueprint: `lem-sc-brauer-zero-all-curves`, Step 2) -/
theorem subsingleton_cohomologicalBrauerGroup_of_isReduced (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsReduced C] : Subsingleton C.CohomologicalBrauerGroup := by
  sorry

end AlgebraicGeometry.IsCurve
