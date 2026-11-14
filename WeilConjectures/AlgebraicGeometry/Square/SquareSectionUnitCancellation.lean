/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageSectionUnit
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareUnitMap
public import WeilConjectures.AlgebraicGeometry.Square.SquareResolutionRoofModels
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.Square.SquareSectionUnitForward

/-! # Cancelling the normalized square on a cochain section unit

Source: Stacks Project, Cohomology, Tags 0D5T and 0D5X.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- A square transports the canonical section unit to the identity on the upstairs
section complex, on the target injective representative.
Source: Stacks Project, Tags 0D5T and 0D5X. -/
theorem squareSectionUnit_cancellation {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (G : Z.Modules) (J : InjectiveResolution G) (q : ℕ) (V : S.Opens) :
    let U := f ⁻¹ᵁ V
    let t := (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnitQ
       J.cochainComplex ≫
        (schemeDerivedDirectImage v).map (inv (DerivedCategory.Q.map J.ι'))
    directImageSectionUnitAt f (q : ℤ) V
        (((pushforward v).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map
        ((schemeDerivedDirectImage f).map t ≫
          (derivedSquareRightComparison f k g v h).hom.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).app (op V) ≫
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInverseOpenComparison g (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J (v ⁻¹ᵁ U) (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).inv = 𝟙 _ := by
  dsimp only
  apply (cancel_mono (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J
    (v ⁻¹ᵁ (f ⁻¹ᵁ V)) (by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact squareSectionUnit_forward f k g v h G J q V

end AlgebraicGeometry
