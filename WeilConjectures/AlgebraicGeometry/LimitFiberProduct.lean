/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Fibre products and quasi-compact opens in inverse limits

## Main results

- `CategoryTheory.IsPullback.isPullback_map_of_isLimit` (blueprint
  `lem-kun-fibre-product-limits`): in any category, a limit of cartesian squares is cartesian;
  in particular inverse limits of schemes commute with fibre products.
- `CategoryTheory.Limits.limitPullbackIso`: the canonical comparison
  `lim (Xᵢ ×_{Sᵢ} Yᵢ) ≅ (lim Xᵢ) ×_{lim Sᵢ} (lim Yᵢ)`.
- `AlgebraicGeometry.Scheme.exists_preimage_eq_of_isAffine` (blueprint
  `lem-kun-descent-limit-open`): a quasi-compact open of a cofiltered limit of affine schemes
  descends to a quasi-compact open of some stage.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

variable {J : Type*} [Category J] {C : Type*} [Category C]

namespace Limits

variable [HasLimitsOfShape J C] [HasPullbacks C]

end Limits

end CategoryTheory

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})

/-- Blueprint `lem-kun-descent-limit-open`: **descent of a quasi-compact open in an affine
limit.** Let `X = lim Xᵢ` be a cofiltered limit of affine schemes (so that all transition maps
are affine) and `U ⊆ X` a quasi-compact open. Then there are an index `i` and a quasi-compact open
`Uᵢ ⊆ Xᵢ` with `U = pᵢ⁻¹(Uᵢ)`. Write `U` as a finite union of basic opens `D(fₖ)`; the finitely
many `fₖ` all come from a common stage `Aᵢ`. -/
theorem Scheme.exists_preimage_eq_of_isAffine [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
    {c : Cone D} (hc : IsLimit c) (U : c.pt.Opens) (hU : IsCompact (U : Set c.pt)) :
    ∃ (i : I) (Uᵢ : (D.obj i).Opens), IsCompact (Uᵢ : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ Uᵢ = U :=
  exists_preimage_eq D c hc U hU

end AlgebraicGeometry
