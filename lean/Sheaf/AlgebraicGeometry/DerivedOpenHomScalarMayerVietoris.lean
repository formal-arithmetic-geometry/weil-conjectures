/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedGlobalScalar
import Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison

/-! # Scalar compatible Mayer--Vietoris on an open union

Source: Stacks Project, Tag 08BW, used in Tag 08EJ.
(blueprint: lem-sc-derived-open-hom-scalar-mayer-vietoris).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The boundary for Hom on an open union commutes with global scalar endomorphisms.
Its preceding term is Hom into the negative shift on the overlap. No compactness,
perfectness, quasi-coherence or support hypothesis is required.
Source: Stacks Project, Tag 08BW and the globalization paragraph of Tag 08EJ.
(blueprint: lem-sc-derived-open-hom-scalar-mayer-vietoris).

Proof: Apply the derived Hom Mayer--Vietoris sequence on W = U union V, using the
localized sites over U, V and their intersection. Associativity of restriction gives
the displayed restriction maps from the W term. The preceding negative Ext term is
identified, by the canonical shift comparison and shift-addition isomorphisms, with
Hom from E on the overlap into E'[k-1] there. Exactness at the W term gives the lift.
The sequence is natural contravariantly in E: in the triangle construction the boundary
is composition with the triangle's connecting morphism, and the extension/restriction
adjunction is natural. Apply this naturality to r times identity on the global E.
Restriction of this endomorphism is multiplication by the restricted r. This proves the
last equation, for every r, with the same additive boundary. Empty opens and k=0 are
included by the same triangle and shift identifications. -/
theorem derived_open_hom_scalar_mayer_vietoris
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U V : X.Opens) (E E' : schemeDerivedCategory X) (k : ℤ) :
    let R := fun W : X.Opens ↦
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    ∃ δ : ((R (U ⊓ V)).obj E ⟶ (R (U ⊓ V)).obj (E'⟦k - 1⟧)) →+
        ((R (U ⊔ V)).obj E ⟶ (R (U ⊔ V)).obj (E'⟦k⟧)),
      (∀ β : (R (U ⊔ V)).obj E ⟶ (R (U ⊔ V)).obj (E'⟦k⟧),
        derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left) β = 0 →
        derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right) β = 0 →
        ∃ γ, δ γ = β) ∧
      ∀ (r : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})) γ,
        δ ((R (U ⊓ V)).map (schemeDerivedScalar X r (𝟙 E)) ≫ γ) =
          (R (U ⊔ V)).map (schemeDerivedScalar X r (𝟙 E)) ≫ δ γ := by sorry

end AlgebraicGeometry
