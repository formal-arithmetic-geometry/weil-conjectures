/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData
import Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle

/-! Canonical compatibility for relative Mayer--Vietoris.
Source: Stacks Project, Tags 08BV, 08HY and 0DJ9. -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Naturality of the concrete SES boundary under pullback to the inverse-image
cover, before applying any further direct image. All shifts and SES comparisons
are the fixed constructions, and the overlap morphism is the pinned open mate.
Source: Stacks Tags 08BV, 08HY and 0DJ9, relative Mayer--Vietoris diagram.
(blueprint: lem-pc-rf-mv-canonical-boundary-pullback).

Proof: represent K by schemeMVResolution and transpose ψ under the pinned
Lg'^* / Rg'_* adjunction. Compute Rg'_*K' using the fixed K-injective resolution
of K', followed by a K-injective replacement of its direct-image complex. A
chain map represents the transposed derived morphism into this replacement.
Restrict it to U, V and their intersection. These restrictions give a morphism
of the concrete short exact Mayer--Vietoris sequences. The direct-image sequence
of the target cover is termwise split: the first term is injective in each degree,
so its monomorphism splits. Applying direct image preserves this splitting.
All three target complexes are K-injective: the first is the fixed resolution;
open restriction preserves K-injectivity by lem-sc-derived-k-injective-restrict-open;
open direct image preserves it by lem-weil-pbc-right-adjoint-preserves-kinjective
because its left adjoint, open restriction, is exact; and finite biproducts preserve
it by additivity of Hom from acyclic complexes.
Consequently its SES boundary computes Rg'_* of the target SES boundary with
the existing right-derived shift. Apply triangleOfSESδ_naturality and transport
by the fixed resolution and open comparisons. On sections, inverse-image cover
restriction agrees with restricting the direct image, so the overlap comparison
is the mate of the pinned pullback/open-restriction comparison; its unit/counit
identities identify the third component with the displayed overlap map. Transpose
back under the pinned g' adjunction. mvCanonicalHomEquiv_shift gives precisely
the constructed pullback shift. This proves the equation on X', without f or f'.
For empty or repeated opens the same SES and chain-map construction applies. -/
theorem mvCanonicalBoundary_pullback
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    letI := mvCanonicalPullbackShift g'
    let δ := mvCanonicalBoundary X U V (U ⊓ V) rfl hcover K
    let δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
      (Scheme.Hom.preimage_inf g').symm
      (by rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]) K'
    (derivedPullback g').map δ ≫
        ((derivedPullback g').commShiftIso (1 : ℤ)).hom.app K ≫ ψ⟦(1 : ℤ)⟧' =
      (schemeDerivedBaseChangeMap (U ⊓ V).ι (g' ⁻¹ᵁ (U ⊓ V)).ι g'
          (g'.resLE (U ⊓ V) (g' ⁻¹ᵁ (U ⊓ V)) le_rfl)
          (Scheme.Hom.resLE_comp_ι g' le_rfl)
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ≫
        (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).map
          ((mvPullbackOpenRestrictionIso g' (U ⊓ V)).inv.app K ≫
            (schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.map ψ)) ≫ δ' := by
  sorry

end AlgebraicGeometry
