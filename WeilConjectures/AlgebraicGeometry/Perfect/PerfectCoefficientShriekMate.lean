/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Algebra.Homology.ProperBaseChange.ConstantCoefficientScalarExtensionPresentations
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientRestrictionCounit
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.RingedTensorEdge.RingedTensorEdgeInducedAdjunction
import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.Sheaf.SheafSliceOrdinaryData
import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceAdjunction
import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData
import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientCounitPresentations
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.ProperBaseChange.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.ProperBaseChange.ContinuousCocontinuousRingedRestriction
import WeilConjectures.CategoryTheory.ProperBaseChange.ElementSiteDescent
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceDerivedComparisons
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceDerivedMate
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.ProperBaseChange.ElementRestrictionHom
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingClassicalGenerator
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerivedLinear

/-! # Perfect coefficients and the exceptional-adjoint mate

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
prop-coef-integral-dualizing.proof.md, paragraph 1; Stacks 0944, 07A4, 07A6 and 0GL6
(blueprint: lem-route-perfect-coefficient-shriek-mate).

All categories below are ordinary unbounded small-etale derived categories. The comparison
is the proper counit mate followed by the open comparison of composite adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical proper/open coefficient arrow for a fixed compactification.
Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 1, and Stacks 0GL6;
its proper factor is the normalized counit mate of Stacks 07A6
(blueprint: lem-route-perfect-coefficient-shriek-mate). -/
def perfectCoefficientCompactSupportMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        SheafOfModules.constantCoefficientEtaleScalarExtension φ Y ⟶
      SheafOfModules.constantCoefficientEtaleScalarExtension φ X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c :=
  Functor.whiskerLeft (derivedExtension (A := A) c.i) (scalarMate φ c.g) ≫
    Functor.whiskerRight (openScalarExtension φ c.i).hom
      R(lowerStar (ModuleCat.{u + 1} B) c.g)

/-- Perfect coefficient change for compact support, including its linear and triangulated
structure and compatibility with integer shifts.
Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 1; Stacks 0944,
07A4, 07A6 and 0GL6 (blueprint: lem-route-perfect-coefficient-shriek-mate).

Proof, following the node's steps:
1. The scalar adjunction has unit x maps to x tensor 1. Exact restriction is conservative
   and identifies restricted extension with tensor by B_T. A bounded finite-projective
   model of B sheafifies exactly, so B_T is perfect (the strict-perfect package and
   lem-weil-pbc-finite-type-constant-exact).
2. For the proper part p, the K-flat-normalized scalar/pullback comparison defines beta
   by transposing scalar extension of the A-counit. The restriction/counit theorem supplies
   kappa, including its counit equation, on all unbounded inputs.
3. That equation and naturality identify kappa after restriction of beta with the actual
   projection map: on K-flat representatives both transposes send x tensor b to b g(x).
4. The arbitrary-ringed-site perfect projection theorem (Stacks 0944) inverts this map.
   Invert kappa, then reflect invertibility through exact coefficient restriction.
5. For the open part, conjugate the exact open/scalar restriction identity. This is the
   published openScalarExtension, with its common-adjunction normalization. Compose its
   proper pushforward with beta to obtain exactly perfectCoefficientCompactSupportMap.
6. For successive perfect algebras, restriction composes canonically; the conjugate scalar
   associator sends (x tensor b) tensor c to x tensor image(b)c. Restricting finite-projective
   models and bounded devissage show the composite algebra is perfect.
7. Transpose the two proper composite coefficient maps. Naturality of pullback comparison
   and its K-flat normalization give equal transposes. Open comparison composes because
   conjugation does. Substitution gives the compact-support composition equation.
8. If exceptional right adjoints exist, compose each with the scalar adjunction. Conjugate
   the inverse of the compact-support comparison. This gives F_A Res_Y to Res_X F_B;
   evaluation gives the asserted objectwise isomorphism.
9. Conjugation reverses composition and preserves inverses. Applying it to step 7 gives
   compatibility of the exceptional mates with successive coefficient extensions.
10. Exact linear open extension descends to a linear triangulated shift-compatible functor.
    Proper direct image has the same structures by its unbounded K-injective total derived
    construction. Compose these structures on the fixed compactification. The integer-shift
    compatibility is the canonical composite `CommShift ℤ` instance of D(j_!) and R(p_*),
    and the triangulated clauses are stated for that instance. -/
theorem routePerfectCoefficientShriekMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (_hB : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)))) :
    IsIso (perfectCoefficientCompactSupportMap φ c) ∧
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).Linear A ∧
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).Linear B ∧
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).IsTriangulated ∧
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).IsTriangulated := by
  sorry

/-- The isomorphism whose hom is precisely the canonical proper/open coefficient map.
Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 1; Stacks 0944, 0GL6
(blueprint: lem-route-perfect-coefficient-shriek-mate). -/
def perfectCoefficientCompactSupportIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (hB : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)))) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ≅
      scalarExtension φ X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c :=
  @asIso _ _ _ _ (perfectCoefficientCompactSupportMap φ c)
    (routePerfectCoefficientShriekMate φ f c hB).1

/-- The specified exceptional mate is the conjugate of the inverse compact-support iso.
Its value at N is F_A(Res_Y N) isomorphic to Res_X(F_B N).
Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 1; Stacks 07A6
(blueprint: lem-route-perfect-coefficient-shriek-mate). -/
def perfectCoefficientExceptionalIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (hB : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))))
    {FA : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
    {FB : DerivedCategoryModule B Y ⥤ DerivedCategoryModule B X}
    (aA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ FA)
    (aB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ FB) :
    Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ ⋙ FA ≅
      FB ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ :=
  conjugateIsoEquiv
    (aA.comp (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)))
    ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).comp aB)
    (perfectCoefficientCompactSupportIso φ f c hB).symm

end AlgebraicGeometry.Etale
