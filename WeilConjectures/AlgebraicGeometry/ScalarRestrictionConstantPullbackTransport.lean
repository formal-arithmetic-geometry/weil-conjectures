/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ScalarRestrictionConstantPullbackUnderived

/-! Derived transport of the ordinary scalar restriction/constant pullback square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Derived localization transport for the ordinary scalar restriction/pullback square.

Source: the exact-functor localization factors in Stacks 0F1E and 0FPI.
The ordinary square is first lifted with
`mapDerivedCategorySquareIso_hom_app_comp`; the comparison isomorphisms for
left-derived upper star and for the derived constant functors are then
cancelled in the displayed order.
Proof (in words): the left-derived upper stars are identified with the
levelwise `mapDerivedCategory` functors by `leftDerivedUpperStarIsoMapDerivedCategory`;
after that identification `scalarRestrictionPullbackIso` and
`derivedConstantSheafCompLeftDerivedUpperStarIso` are `mapDerivedCategory` of the
ordinary isomorphisms `upperStarRestrictScalarsIsoSheaf` and
`constantSheafCompUpperStarNatIso`, so both sides are `mapDerivedCategory` (composed with
`mapDerivedCategoryCompIso`) of the two sides of the ordinary square `h`, and they agree.
(blueprint: new-lem-pur-scalar-restriction-constant-pullback-transport).
-/
theorem scalarRestrictionConstantPullback_transport
    {Z T : Scheme.{u}} (p : Z ⟶ T)
    (h : ∀ X : ModuleCat.{u + 1} B,
      (constantSheafCompSheafComposeIso Z.smallEtaleTopology
        (ModuleCat.restrictScalars φ)).inv.app X ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).map
          ((constantSheafCompUpperStarNatIso (ModuleCat.{u + 1} B) p).inv.app X) =
      (constantSheafCompUpperStarNatIso (ModuleCat.{u + 1} A) p).inv.app
          ((ModuleCat.restrictScalars φ).obj X) ≫
        (upperStar (ModuleCat.{u + 1} A) p).map
          ((constantSheafCompSheafComposeIso T.smallEtaleTopology
            (ModuleCat.restrictScalars φ)).inv.app X) ≫
        (upperStarRestrictScalarsIsoSheaf φ p).hom.app
          ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)).obj X))
    (H : DerivedCategory (ModuleCat.{u + 1} B)) :
    let U₀ := (ModuleCat.restrictScalars φ).mapDerivedCategory
    let UZ := Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ
    let pA := (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
    let σT := (Functor.mapDerivedCategorySquareIso
      (constantSheafCompSheafComposeIso T.smallEtaleTopology
        (ModuleCat.restrictScalars φ)).symm).hom
    let σZ := (Functor.mapDerivedCategorySquareIso
      (constantSheafCompSheafComposeIso Z.smallEtaleTopology
        (ModuleCat.restrictScalars φ)).symm).hom
    (derivedConstantSheafCompLeftDerivedUpperStarIso
        (ModuleCat.{u + 1} A) p).inv.app (U₀.obj H) ≫
      pA.map (σT.app H) ≫
      (scalarRestrictionPullbackIso φ p).hom.app
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj H) =
    σZ.app H ≫ UZ.map ((derivedConstantSheafCompLeftDerivedUpperStarIso
      (ModuleCat.{u + 1} B) p).inv.app H) := by
  sorry

end AlgebraicGeometry.Etale
