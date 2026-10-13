/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Transporting K-flat coordinates to opens

Source: Stacks Project, Tags 0DJ9, 08HY, and 08FE.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Transport one K-flat coordinate system to compatible target opens.
This concerns the comparison in these coordinates, not the universally quantified
stalk condition and not the base-change arrow.
Source: Stacks Project, perfect.tex, Tag 0DJ9, first paragraph, and equation-bc
preceding Tag 0DJ8; Cohomology, Tag 06YC.
(blueprint: lem-pc-single-complex-open-coordinate-transport).

Proof: Restrict P and N termwise to U and U'. Exact restriction transports e and e'
through the localization comparison. K-flatness of P|U follows from the stalk
criterion: its stalk at a point of U is the original K-flat stalk. The pinned
left-derived counit computes tensor pullback on this K-flat complex. The ordinary
pullback composition comparison and the open-pullback adjunction comparison
identify the restriction of t with a map from tensor pullback of P|U to N|U'.
The leftDerivedUnique factorization equation identifies its representing equation
with the displayed constructed restricted coefficient. These give coordinates d.
For z in U', use open-immersion stalk isomorphisms on all four local rings. Their
compatibility with the scheme stalk maps identifies the tensor-product algebra and
its map to C, and the stalks of P|U and N|U' identify with those of P and N.
The localized tensor comparison is natural under these ring and complex
isomorphisms. The tensor-pullback stalk comparison and the homology map of the
restricted t commute with the same identifications. Thus the two stalkComparison
maps are conjugate by isomorphisms; invertibility is equivalent. Empty opens have
no points, and this computation imposes no boundedness or affineness. -/
theorem singleComplexOpen_coordinates_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (c : SingleComplexBaseChange.Coordinates g' K K' φ)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV')) :
    let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
    let K₀' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.obj K'
    let φ₀ := singleComplexRestrictedCoefficient g' K K' φ
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    ∃ d : SingleComplexBaseChange.Coordinates j K₀ K₀' φ₀,
      ∀ (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ),
        IsIso (SingleComplexBaseChange.stalkComparison
          (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ d z i) ↔
        IsIso (SingleComplexBaseChange.stalkComparison f f' g g' sq c z.val i) := by sorry

end AlgebraicGeometry
