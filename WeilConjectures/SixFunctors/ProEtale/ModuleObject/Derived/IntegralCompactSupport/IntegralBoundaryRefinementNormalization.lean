/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle

/-! # Total-derived normalization of a single boundary refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
set_option synthInstance.maxSize 2048

attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
attribute [local instance 2000] CategoryTheory.scalarTensor4 CategoryTheory.scalarTensor12
  CategoryTheory.scalarTensor23 CategoryTheory.scalarTensorColimits
  CategoryTheory.scalarFlipTensorColimits CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
attribute [local irreducible] HasDerivedCategory.standard

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar openImmersionLowerShriek
  derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  localizing localizingClosureProEtale CategoryTheory.localizingClosure
  compactificationRefinementComponent localizingRefinementMap
  pushComp refinementDerivedLowerStarComp
  Adjunction.ofNatIsoRight upperStarComp

section Coefficients

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (k : Type u) [Field k]

/-- The proper-open refinement map on Loc is invertible and its normalization transports
from the exact open adjunction to the total-derived open adjunction.

Source: blueprint det-sf-comp-coherence-refinement, clauses (1)--(3), and
lem-sfb-total-derived-normalized-comparisons, inverse-component step.
(blueprint: lem-sfb-boundary-refinement-total-normalization).

Proof: use the supplied Loc(Dctf) membership of K (the caller obtains it from
Loc(Dbc) by the equality of localizing closures). Dominate the source compactification
by a common dense refinement with itself.
The localizing refinement maps for that refinement and its composite with r are
invertible by boundary vanishing; their composition law cancels the first to prove
invertibility of the map for r. Take e to be the isomorphism of that canonical map.
Transport localizingRefinementMap_normalized along the canonical isomorphism between
termwise and total pullback. Naturality cancels the transport factors, giving the
unit equation displayed here. Identify pushComp with the inverse recorded derived
pushforward compositor by conjugating the pullback compositor under the derived
adjunctions. Expand the inverse of refinementIso: its three factors are Rp_* of e,
the inverse compositor, and the pushforward equality transport, exactly the factors
of compactificationRefinementComponent. No density of c or d is used, and empty
opens and zero objects satisfy the same equations. -/
theorem integral_boundaryRefinement_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (hadm : IsLocalizingAdmissibleCoefficient ℓ Λ)
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (hb : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing Λ X.obj.left).FullSubcategory)
    (hK : localizingClosureProEtale Λ X.obj.left K.obj) :
    ∃ e : (extend Λ d.obj.i).obj K.obj ≅
        (push Λ r.hom).obj ((extend Λ c.obj.i).obj K.obj),
      (openAdjunction Λ d.obj.i).homEquiv _ _ e.hom ≫
          refinementRestriction Λ r K.obj = (openAdjunction Λ c.obj.i).unit.app K.obj ∧
      HEq (refinementIso Λ r K.obj e).inv
        (compactificationRefinementComponent Λ
          (⟨ObjectProperty.homMk r, hb⟩ :
            (⟨c⟩ : Compactification.BoundaryCompactification f.hom.left) ⟶ ⟨d⟩) K.obj) := by
  sorry

end Coefficients
end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
