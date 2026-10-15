/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapLocalSiteTriangle
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport

/-! # Canonical gamma comparison on the first open -/

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
-- The statement names the derived categories on both nested opens.
/-- The canonical gamma component followed by the local composite comparison
is the intersection pullback of the named local map.
Source: Stacks Project, Tags 08BV, 08DW and 0D5S. The gamma component is
determined on a global lift by the two beta comparisons. Their pinned open
square formulas expose the return maps, which cancel by the inverse return
triangle. Naturality of the overlap-site equivalence then moves the local
three-step composite to the intersection and cancels its inverse component. -/
theorem perfectOverlapCanonicalGammaLocalU
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (F : schemeDerivedCategory K)
    (e : (schemeOpenRestriction K (f ⁻¹ᵁ U)).mapDerivedCategory.obj F ≅
      (derivedPullback (f ∣_ U)).obj A) :
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let hPU : P ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let hPV : Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let d := schemeComparisonFromRestrictions gk (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
      P Q hPU hPV
    let diagram := d.toDiagram
    let i : P ⊓ Q ⟶ P := homOfLE inf_le_left
    let iK : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ U := homOfLE inf_le_left
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let LU := (overlapSiteInverse P).mapDerivedCategory
    let LW := (overlapSiteInverse (P ⊓ Q)).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction K iK).mapDerivedCategory
    let SX := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let hPW : P ⊓ Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) :=
      fun _ hx ↦ ⟨hPU hx.1, hPV hx.2⟩
    let squareW := singleComplexOpenPullbackSquareIso gk
      (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q)
      (gk.resLE (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) hPW)
      (Scheme.Hom.resLE_comp_ι gk hPW)
    let κ := perfectOverlapCompositeLocalIso f gk g hgf U
    let ω := openSiteOverlapIso X i
    let t := perfectOverlapCompositeLocalMap g gk f hgf U A F e
    diagram.γU.inv.app ((derivedPullback (f ∣_ U)).obj A) ≫
      SP.map (LU.map (κ.hom.app A)) ≫
        ω.hom.app ((derivedPullback (g ∣_ U)).obj A) =
      (SU ⋙ diagram.HW).map e.inv ≫
        diagram.HW.map ((schemeDerivedOpenRestrictionCompIso K iK).hom.app F) ≫
          LW.map (squareW.hom.app F) ≫
            LW.map ((schemeDerivedOpenRestrictionCompIso X i).inv.app
              ((derivedPullback gk).obj F)) ≫
              LW.map (SX.map t) := by
  intro P Q hPU hPV d diagram i iK SP LU LW SU SX hPW squareW κ ω t
  have hγ := overlapNatIso_inv_app_of_iso _ _ diagram.γU e
  rw [overlapDiagram_gammaU_inv_on_image diagram F] at hγ
  have hβU : diagram.βU = perfectOverlapRestrictionBeta gk (f ⁻¹ᵁ U) P hPU := by
    simpa only [diagram, d] using
      (schemeComparisonFromRestrictions_betaU gk (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        P Q hPU hPV)
  have hβW : diagram.βW = perfectOverlapRestrictionBeta gk
      (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) hPW := by
    simpa only [diagram, d] using
      (schemeComparisonFromRestrictions_betaW gk (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        P Q hPU hPV)
  rw [congrArg (fun z => z.inv.app F) hβW,
    congrArg (fun z => z.hom.app F) hβU] at hγ
  rw [perfectOverlapRestrictionBeta_inv_app_square,
    perfectOverlapRestrictionBeta_hom_app_square] at hγ
  simp only [Functor.map_comp, Category.assoc] at hγ
  have hreturn := openSiteReturn_overlap_triangle_inv_app X i
    ((derivedPullback gk).obj F)
  conv at hγ =>
    rhs
    slice 4 6
    exact hreturn
  simp only [Functor.comp_map, Category.assoc] at hγ
  have hsite := perfectOverlapLocalSiteTriangleU g gk f hgf U V A F e
  let tail := SP.map (LU.map (κ.hom.app A)) ≫
    ω.hom.app ((derivedPullback (g ∣_ U)).obj A)
  have hγ' := congrArg (fun z => z ≫ tail) hγ
  dsimp only [tail] at hγ'
  conv at hγ' =>
    rhs
    slice 5 9
    exact hsite
  simpa only [Functor.comp_map, Category.assoc, SU, LW, squareW] using hγ'

end AlgebraicGeometry
