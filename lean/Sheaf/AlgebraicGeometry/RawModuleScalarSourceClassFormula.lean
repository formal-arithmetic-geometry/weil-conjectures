/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted
import Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition
import Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquareCore

/-! # Source and class coherence before coefficients

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-module-scalar-source-class-formula).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Commute the source and class factors before attaching any coefficient tail.
Source: Stacks Project, Tags 03D7 and 03Q8, scalar inverse-image composition.
(blueprint: lem-sbc-raw-module-scalar-source-class-formula).

Proof: Apply rawModuleScalar_sheaf_composition to the free represented module
sheaf. Naturality of upperStarComp on the free abelian generator attaches that
generator to its source square. Apply plus_single_source_square_core in degree
zero to derive the square. Its factors are scalarSourceFactor, moduleSourceFactor
and abelianSourceFactor, and its comparison is derivedPullbackIso. Postcompose
this square with derived scalar forgetting of the derived inverse image of z.
Naturality of the inverse derivedPullbackIso on z moves z across the inverse
comparison. Functor.map_comp combines the abelian inverse images of the source
map and forgotten class into rawModuleScalarSourcePrefix. Reassociate. No
moduleCoefficientFactor, scalarCoefficientFactor or coefficient coherence is
used in this equation. Zero classes, q = 0, identity arrows, zero and empty
objects satisfy the same functoriality and naturality equations.
-/
theorem rawModuleScalar_source_class_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      (RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦(q : ℤ)⟧) := by sorry

end AlgebraicGeometry.Etale
