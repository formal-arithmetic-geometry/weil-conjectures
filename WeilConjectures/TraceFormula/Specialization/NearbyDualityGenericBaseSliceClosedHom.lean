/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.GenericRestriction.GenericFibre
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs

/-!

# The pullbacks to a generic slice commute with internal Hom

For the generic slice of a trait model over a generic base along a coordinate `b`, the pullbacks
along the special-fibre map `p : 𝒳''_s ⟶ X'` and the generic-fibre map `c : X₂ ⟶ X₁` commute
with internal Hom
(`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_closedHomComparison_sliceSpecialUpperStar`,
`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_closedHomComparison_genericSliceUpperStar`).
This is blueprint `det-pd-generic-closed-hom` (2), of the six-functor chapter
(`sk-lem-pd-generic-restriction`), stated here for the two pullbacks; it is proved there.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

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

/-- **The pullback to the special fibre of a generic slice commutes with internal Hom**
(blueprint `det-pd-generic-closed-hom` (2), for the geometric generic fibre
`𝒳''_s = 𝒳_s ×_{𝔸¹_{k'}} Spec K` of the coordinate): the comparison
`p^* RHom(A, ω_{X'}) ⟶ RHom(p^* A, p^* ω_{X'})` is an isomorphism. -/
theorem isIso_closedHomComparison_sliceSpecialUpperStar
    (A : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (Functor.LaxMonoidal.μ (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb))
      (𝟙 ((sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X'))) A) := by
  sorry

/-- **The pullback to the base of a generic slice commutes with internal Hom** (blueprint
`det-pd-generic-closed-hom` (2), on the generic fibres): the comparison
`c^* RHom(A, ω_{X₁}) ⟶ RHom(c^* A, c^* ω_{X₁})` is an isomorphism. -/
theorem isIso_closedHomComparison_genericSliceUpperStar
    (A : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (Functor.LaxMonoidal.μ (genericSliceUpperStar (traitSliceCoord k') ℓ h hb))
      (𝟙 ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁))) A) := by
  sorry

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
