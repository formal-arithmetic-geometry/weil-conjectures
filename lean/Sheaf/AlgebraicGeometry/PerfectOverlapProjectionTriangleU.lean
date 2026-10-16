/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareCube
public import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenLiftComponents
public import Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalOpenPrismU
public import Sheaf.AlgebraicGeometry.PerfectOverlapProjectionPrism
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageObjectTail
public import Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrismHom
public import Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositeAbstract
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageSchemeIso

/-! # Projection triangle for the first canonical overlap object -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

set_option maxHeartbeats 8000000 in
-- The fixed comparison and both stage object maps contain nested pullbacks.
/-- The first-open projection map for a global coefficient is compatible with
the restricted composite.
Source: Stacks Project, Tags 0D5S and 08DW.

Proof: Naturality of the cartesian comparison moves the lifted-object
isomorphism to the stage. The pinned open-pullback cube identifies the two
orders of restricting the global lift and pulling it back along the composite
map. The defining component equation for the local composite comparison
cancels the first-open square and its inverse. The two residual paths are the
two associations of the same three derived pullbacks. Their equality is the
associativity clause of the fixed pullback-composition comparison. The
cartesian equation `hmap` identifies their scheme maps, and the fixed
`perfectHomComparison` identifies the final projection. -/
theorem perfectOverlapProjectionTriangleGlobalU
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S) (l : Over.mk b ⟶ Over.mk q)
    (hgf : gk ≫ f = g) (hg : IsPullback g pX pY b)
    (hf : IsPullback f pK pY q) (U V : Y.Opens)
    (hR : g ⁻¹ᵁ (U ⊓ V) ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ (U ⊓ V)))
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫
          gk.resLE (f ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ (U ⊓ V)) hR =
        baseChangeMap ((U ⊓ V).ι ≫ pY) l ≫
          ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv)
    (M : schemeDerivedCategory Y) :
    let A := (schemeOpenRestriction Y U).mapDerivedCategory.obj M
    let F := (derivedPullback f).obj M
    let e := perfectOverlapOpenLiftBeta f U M
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let hPU : P ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let hPV : Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let hPW : P ⊓ Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) :=
      fun _ hx ↦ ⟨hPU hx.1, hPV hx.2⟩
    let rW := gk.resLE (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) hPW
    let i : P ⊓ Q ⟶ P := homOfLE inf_le_left
    let iK : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ U := homOfLE inf_le_left
    let SU := (schemeOpenOverlapRestriction K iK).mapDerivedCategory
    let SX := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let squareW := singleComplexOpenPullbackSquareIso gk
      (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) rW (Scheme.Hom.resLE_comp_ι gk hPW)
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    let r := gk.resLE (f ⁻¹ᵁ (U ⊓ V)) (g ⁻¹ᵁ (U ⊓ V)) hR
    let m := baseChangeMap ((U ⊓ V).ι ≫ pY) l
    let eY := ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
    let eK := ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback
    let comparison := perfectOverlapDerivedPullbackTransport r eY eK m hmap
    let a := (derivedPullback rW).map (SU.map e.inv)
    let z := (derivedPullback rW).map
      ((schemeDerivedOpenRestrictionCompIso K iK).hom.app F)
    let c := squareW.hom.app F
    let d := (schemeDerivedOpenRestrictionCompIso X i).inv.app
      ((derivedPullback gk).obj F)
    let t := SX.map (perfectOverlapCompositeLocalMap g gk f hgf U A F e)
    cart.functor.map a ≫ cart.functor.map z ≫ cart.functor.map c ≫
      cart.functor.map d ≫ cart.functor.map t ≫
        ((perfectOverlapStageObjectIso g pX pY b hg U V U inf_le_left).app A).hom ≫
          (perfectHomComparison ((U ⊓ V).ι ≫ pY) l).hom.app
            ((derivedPullback (Y.homOfLE inf_le_left)).obj A) =
      comparison.hom.app (SU.obj ((derivedPullback (f ∣_ U)).obj A)) ≫
        (derivedPullback m).map
          ((perfectOverlapStageObjectIso f pK pY q hf U V U inf_le_left).app A).hom := by
  sorry

end AlgebraicGeometry
