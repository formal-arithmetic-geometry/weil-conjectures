/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageSectionUnit
public import Sheaf.AlgebraicGeometry.DerivedSquareUnitMap
public import Sheaf.AlgebraicGeometry.SquareResolutionRoofModels
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Forward normalized square comparison before endpoint cancellation

Source: Stacks Project, Cohomology, Tags 0D5T and 0D5X.
(blueprint: lem-weil-pbc-square-section-unit-forward).
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

/-- The normalized square comparison reaches the raw target endpoint before its
inverse is applied. This is the forward equation needed for cancellation in the
section-unit identity.
Source: Stacks Project, Tags 0D5T and 0D5X
(blueprint: lem-weil-pbc-square-section-unit-forward).

Proof: Resolve the target coefficient by J, use the right-derived mate equation for
the commuting square, and evaluate the universal Leray and inverse-open
factorizations on the same K-injective representative. The resulting map is the
hom of `squareInjectiveLocalComparison` for k. This is the forward half of the
unit cancellation; postcomposition with its inverse gives the parent statement.
The construction is valid for empty opens and identity squares.
-/
theorem squareSectionUnit_forward {X S Z T : Scheme.{u}}
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
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) =
      (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J (v ⁻¹ᵁ U) (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).hom := by
  sorry

end AlgebraicGeometry
