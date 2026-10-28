/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalCoefficientFiniteRealization
public import Sheaf.Paper.DiagonalCoefficientUnitPush

/-! # The finite constant coefficient adjunct in degree zero -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- A unital map from the constant rank-one module to its ordinary direct image
represents the canonical finite unit adjunct after the single-complex and finite
constant comparisons. Source: diagonal tower coefficient changes (1), ordinary
constant units and the canonical derived adjunction.
(blueprint: lem-diagonal-finite-constant-adjunct).

Proof: the constant-sheaf adjunction identifies maps out of the constant rank-one
module with module maps out of A on terminal sections. Such a module map is determined
by the image of one. The hypothesis identifies that image with constant one on the
projective line, so m is the adjunct of the canonical constant-sheaf pullback
isomorphism. The canonical derived adjunction, evaluated on the single complex,
is the single of this ordinary adjunct followed by the right-derived unit. This
follows from the derived counit factorization and the ordinary triangle identity.
Finally the comparison inverse image and both geometric inverse images preserve
constant sheaves by uniqueness of their left adjoints to sections. Naturality and
uniqueness of these left-adjoint comparisons identify the constant pullback just
used with geoP1UnitPullback under finiteUnitComparison. Substituting this identity
into the derived hom-equivalence proves the equation. These arguments also apply
on the empty scheme and over the zero ring. -/
theorem finite_constant_adjunct_of_one
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (m : geoCartierConstant A Y ⟶
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    (h : (@MonObj.one _ _ _ (finiteConstantAbRing A Y)
        ((sfbConstantRing Y).obj (RingCat.of A)).mon) ≫ (finiteConstantAbComparison A Y).inv ≫
        (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map m ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (finiteConstantAbComparison A (ProjectiveLine Y)).hom =
      Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)) ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (@MonObj.one _ _ _ (finiteConstantAbRing A (ProjectiveLine Y))
        ((sfbConstantRing (ProjectiveLine Y)).obj (RingCat.of A)).mon)) :
    (DerivedCategory.singleFunctor _ 0).map m ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y))
          (.up ℤ) 0).inv.app (geoCartierConstant A (ProjectiveLine Y))) ≫
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).rightDerivedFunctorUnitQ
        ((HomologicalComplex.single _ (.up ℤ) 0).obj
          (geoCartierConstant A (ProjectiveLine Y))) ≫
      (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map
        (finiteUnitComparison A (ProjectiveLine Y)).inv =
    (finiteUnitComparison A Y).inv ≫ finiteUnitAdjunct A Y := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
