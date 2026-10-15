/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareCube

/-! # Local open-site triangle for the canonical overlap map -/

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

/-- The first-open square, lifted-object map, and restricted-composite map
pass through the open-site overlap comparison as one local morphism.
Source: Stacks Project, Tags 08BV and 0D5S. Naturality of the overlap-site
isomorphism moves the three-factor composite across it; the inverse and
forward components cancel, leaving the intersection restriction of that
composite. -/
theorem perfectOverlapLocalSiteTriangleU
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (F : schemeDerivedCategory K)
    (e : (schemeOpenRestriction K (f ⁻¹ᵁ U)).mapDerivedCategory.obj F ≅
      (derivedPullback (f ∣_ U)).obj A) :
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let i : P ⊓ Q ⟶ P := homOfLE inf_le_left
    let hP : P ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let j := gk.resLE (f ⁻¹ᵁ U) P hP
    let LU := (overlapSiteInverse P).mapDerivedCategory
    let LW := (overlapSiteInverse (P ⊓ Q)).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let square := singleComplexOpenPullbackSquareIso gk (f ⁻¹ᵁ U) P j
      (Scheme.Hom.resLE_comp_ι gk hP)
    let κ := perfectOverlapCompositeLocalIso f gk g hgf U
    let t := perfectOverlapCompositeLocalMap g gk f hgf U A F e
    (openSiteOverlapIso X i).inv.app
        ((schemeOpenRestriction X P).mapDerivedCategory.obj ((derivedPullback gk).obj F)) ≫
      SP.map (LU.map (square.inv.app F)) ≫
        SP.map (LU.map ((derivedPullback j).map e.hom)) ≫
          SP.map (LU.map (κ.hom.app A)) ≫
            (openSiteOverlapIso X i).hom.app ((derivedPullback (g ∣_ U)).obj A) =
      LW.map (SU.map t) := by
  intro P Q i hP j LU LW SP SU square κ t
  have ht := perfectOverlapCompositeLocalMap_eq g gk f hgf U A F e
  have hn := openSiteOverlap_inv_map_hom X i t
  have ht' : t = square.inv.app F ≫ (derivedPullback j).map e.hom ≫
      κ.hom.app A := by
    simpa only [t, square, j, κ] using ht
  have hlocal : SP.map (LU.map t) =
      SP.map (LU.map (square.inv.app F)) ≫
        SP.map (LU.map ((derivedPullback j).map e.hom)) ≫
          SP.map (LU.map (κ.hom.app A)) := by
    rw [ht']
    simp only [Functor.map_comp]
  change (openSiteOverlapIso X i).inv.app
      ((schemeOpenRestriction X P).mapDerivedCategory.obj ((derivedPullback gk).obj F)) ≫
    SP.map (LU.map t) ≫
      (openSiteOverlapIso X i).hom.app ((derivedPullback (g ∣_ U)).obj A) =
        LW.map (SU.map t) at hn
  rw [hlocal] at hn
  simpa only [Category.assoc] using hn

end AlgebraicGeometry
