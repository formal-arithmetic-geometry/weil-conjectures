/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs

/-!

# The dualizing complexes of a generic slice

For the generic slice of a trait model over a generic base along a coordinate `b`, the pullbacks
of the dualizing complexes along the generic-fibre map `c : X₂ ⟶ X₁` and the special-fibre map
`p : 𝒳''_s ⟶ X'` are the dualizing complexes of the slice twisted by `ℚ̄_ℓ(1)[2]`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_dualizingComplex_genericSlice_twist`,
blueprint `det-pd-generic-dualizing-twist`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

namespace IsTraitModelOfGenericBase

/-- **The dualizing complex on a generic fibre is twisted** (blueprint
`det-pd-generic-dualizing-twist`, section `sk-lem-pd-generic-restriction` of the six-functor
chapter). Restricting to the fibre of a coordinate over the generic point of the affine line
twists the dualizing complex by `ℚ̄_ℓ(1)[2]`: on the generic fibres,
`c^* ω_{X₁} ≅ ω_{X₂}(1)[2]` (`X₂` the fibre of `b_η` over the generic point
`Spec Frac K⟦t⟧ ⟶ 𝔸¹_η`, after the base change of fields `F ⟶ Frac k'⟦t⟧`, which does not
twist), and on the special fibres `p^* ω_{X'} ≅ ω_{𝒳''_s}(1)[2]` (`𝒳''_s` the fibre of
`b_s` over the geometric generic point `Spec K ⟶ 𝔸¹_{k'}`). -/
theorem exists_dualizingComplex_genericSlice_twist :
    Nonempty ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 1 2) ∧
      Nonempty ((sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
            1 2) :=
  sorry

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
