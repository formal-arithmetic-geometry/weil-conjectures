/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapCounitChain
public import Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalGammaLocal
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence

/-! # Removing the open-site equivalence from the first canonical comparison -/

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
-- The statement contains five derived open-site maps and their counit.
/-- The five local gamma factors pass through the open-site counit as five
scheme-derived maps. Source: Stacks Project, Tags 08BV and 08DW.

Proof: The apex equivalence is the forward open-site equivalence followed by
the cartesian pullback functor. Functoriality exposes the five inverse images.
Naturality of its counit, in `equivalence_counit_five`, moves them across the
terminal counit at once. -/
theorem perfectOverlapCanonicalCounitU
    {X K Y C S : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (pX : X ⟶ C) (pY : Y ⟶ S) (b : C ⟶ S)
    (hg : IsPullback g pX pY b) (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (F : schemeDerivedCategory K)
    (e : (schemeOpenRestriction K (f ⁻¹ᵁ U)).mapDerivedCategory.obj F ≅
      (derivedPullback (f ∣_ U)).obj A) :
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
    let LW := (overlapSiteInverse (P ⊓ Q)).mapDerivedCategory
    let squareW := singleComplexOpenPullbackSquareIso gk
      (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) rW (Scheme.Hom.resLE_comp_ι gk hPW)
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (P ⊓ Q)) ≌
      SheafOfModules.{u} (moduleRings (P ⊓ Q).toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv (P ⊓ Q)
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    let a := (derivedPullback rW).map (SU.map e.inv)
    let z := (derivedPullback rW).map
      ((schemeDerivedOpenRestrictionCompIso K iK).hom.app F)
    let c := squareW.hom.app F
    let d' := (schemeDerivedOpenRestrictionCompIso X i).inv.app
      ((derivedPullback gk).obj F)
    let t := SX.map (perfectOverlapCompositeLocalMap g gk f hgf U A F e)
    apex.functor.map (LW.map a) ≫
      apex.functor.map (LW.map z) ≫
        apex.functor.map (LW.map c) ≫ apex.functor.map (LW.map d') ≫
          apex.functor.map (LW.map t) ≫
            cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app
              (SX.obj ((derivedPullback (g ∣_ U)).obj A))) =
      cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app
          ((derivedPullback rW).obj (SU.obj ((derivedPullback (f ∣_ U)).obj A)))) ≫
        cart.functor.map a ≫ cart.functor.map z ≫ cart.functor.map c ≫
          cart.functor.map d' ≫ cart.functor.map t := by
  intro P Q hPU hPV hPW rW i iK SU SX LW squareW eW cart apex a z c d' t
  have h := equivalence_counit_five eW.mapDerivedCategory cart.functor a z c d' t
  convert h using 1 <;> rfl

set_option maxHeartbeats 8000000 in
-- The two diagram projections elaborate dependent functor maps.
/-- The canonical diagram's two lifted factors satisfy the same counit
pasting. Source: Stacks Project, Tags 08BV and 08DW.

Proof: The named `HW` projection is restricted pullback followed by inverse
open-site transport. Its two component maps therefore equal the corresponding
raw maps. Substituting these component equations gives
`perfectOverlapCanonicalCounitU`. -/
theorem perfectOverlapCanonicalCounitDiagramU
    {X K Y C S : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (pX : X ⟶ C) (pY : Y ⟶ S) (b : C ⟶ S)
    (hg : IsPullback g pX pY b) (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (F : schemeDerivedCategory K)
    (e : (schemeOpenRestriction K (f ⁻¹ᵁ U)).mapDerivedCategory.obj F ≅
      (derivedPullback (f ∣_ U)).obj A) :
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
    let LW := (overlapSiteInverse (P ⊓ Q)).mapDerivedCategory
    let diagram := (schemeComparisonFromRestrictions gk (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
      P Q hPU hPV).toDiagram
    let squareW := singleComplexOpenPullbackSquareIso gk
      (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) rW (Scheme.Hom.resLE_comp_ι gk hPW)
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (P ⊓ Q)) ≌
      SheafOfModules.{u} (moduleRings (P ⊓ Q).toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv (P ⊓ Q)
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    let a := (derivedPullback rW).map (SU.map e.inv)
    let z := (derivedPullback rW).map
      ((schemeDerivedOpenRestrictionCompIso K iK).hom.app F)
    let c := squareW.hom.app F
    let d' := (schemeDerivedOpenRestrictionCompIso X i).inv.app
      ((derivedPullback gk).obj F)
    let t := SX.map (perfectOverlapCompositeLocalMap g gk f hgf U A F e)
    apex.functor.map ((SU ⋙ diagram.HW).map e.inv) ≫
      apex.functor.map (diagram.HW.map
        ((schemeDerivedOpenRestrictionCompIso K iK).hom.app F)) ≫
        apex.functor.map (LW.map c) ≫ apex.functor.map (LW.map d') ≫
          apex.functor.map (LW.map t) ≫
            cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app
              (SX.obj ((derivedPullback (g ∣_ U)).obj A))) =
      cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app
          ((derivedPullback rW).obj (SU.obj ((derivedPullback (f ∣_ U)).obj A)))) ≫
        cart.functor.map a ≫ cart.functor.map z ≫ cart.functor.map c ≫
          cart.functor.map d' ≫ cart.functor.map t := by
  intro P Q hPU hPV hPW rW i iK SU SX LW diagram squareW eW cart apex a z c d' t
  have hfirst : (SU ⋙ diagram.HW).map e.inv = LW.map a := by
    simp only [Functor.comp_map]
    rfl
  have hsecond : diagram.HW.map
      ((schemeDerivedOpenRestrictionCompIso K iK).hom.app F) = LW.map z := by
    rfl
  rw [hfirst, hsecond]
  exact perfectOverlapCanonicalCounitU g gk f hgf pX pY b hg U V A F e

end AlgebraicGeometry
