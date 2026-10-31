/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtensionPresentations
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.PurEtaleScalarMateProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
import WeilConjectures.CategoryTheory.RingedCoefficientRestrictionCounit
import WeilConjectures.AlgebraicGeometry.RingedSitePerfectProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.KInjectiveTotalDerivedLinear

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

/-- The scalar associator, conjugate to the canonical exact restriction compositor.
Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 1; Stacks 07A6
(blueprint: lem-route-perfect-coefficient-shriek-mate). -/
def perfectCoefficientScalarCompIso
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u}) :
    scalarExtension φ T ⋙ scalarExtension ψ T ≅ scalarExtension (ψ.comp φ) T :=
  Adjunction.leftAdjointCompIso
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology (ψ.comp φ)))
    (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology rfl)

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

/-- The canonical compact-support comparisons compose under the scalar associators.
Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 1; Stacks 07A4, 07A6
(blueprint: lem-route-perfect-coefficient-shriek-mate).
Proof: step 7 of routePerfectCoefficientShriekMate. Transpose proper maps under the
geometric adjunction. Their K-flat pullback identifications and counits agree; conjugation
of the common open restriction identity gives the open equality. Naturality pastes them. -/
theorem perfectCoefficientCompactSupportMap_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (_hB : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))))
    (_hC : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} B) 0).obj
        ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of C C))))
    (K : DerivedCategoryModule A X) :
    (perfectCoefficientScalarCompIso φ ψ Y).hom.app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
      (perfectCoefficientCompactSupportMap (ψ.comp φ) c).app K =
    (scalarExtension ψ Y).map ((perfectCoefficientCompactSupportMap φ c).app K) ≫
      (perfectCoefficientCompactSupportMap ψ c).app ((scalarExtension φ X).obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
        ((perfectCoefficientScalarCompIso φ ψ X).hom.app K) := by
  sorry

/-- A composite of perfect coefficient algebras is perfect.
Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 1; Stacks 0ATI
(blueprint: lem-route-perfect-coefficient-shriek-mate).
Proof: step 6 of routePerfectCoefficientShriekMate. By the perfect classical-generator
theorem, perfect A-complexes are the thick envelope P of A, and C lies in the thick
envelope of B. Exact restriction of scalars along φ is a triangulated functor F, so the
inverse image of P under F is triangulated and closed under retracts; it contains B
because F(B) is the perfect A-complex B. Hence it contains C, and F(C) is the restriction
of C along the composite ψ.comp φ. -/
theorem perfectCoefficientAlgebraComp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    (_hB : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))))
    (_hC : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} B) 0).obj
        ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of C C)))) :
    _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((ModuleCat.restrictScalars (ψ.comp φ)).obj (ModuleCat.of C C))) := by
  let F := (ModuleCat.restrictScalars φ).mapDerivedCategory
  let P : ObjectProperty (_root_.DerivedCategory (ModuleCat.{u + 1} A)) :=
    (ObjectProperty.singleton
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        (ModuleCat.of A A))).triangEnvelope
  have hB : P ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))) := by
    change (ObjectProperty.singleton
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        (ModuleCat.of A A))).triangEnvelope
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)))
    rw [← _root_.DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton A]
    exact _hB
  have hC := _hC
  rw [_root_.DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton B] at hC
  have : (P.inverseImage F).IsStableUnderRetracts :=
    ⟨fun r h ↦ P.prop_of_retract (r.map F) h⟩
  have hgen : ObjectProperty.singleton
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} B) 0).obj
        (ModuleCat.of B B)) ≤ P.inverseImage F := by
    apply (ObjectProperty.singleton_le_iff (P := P.inverseImage F)).mpr
    change P (F.obj ((_root_.DerivedCategory.singleFunctor
      (ModuleCat.{u + 1} B) 0).obj (ModuleCat.of B B)))
    have e := ((ModuleCat.restrictScalars φ).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of B B)
    exact P.prop_of_iso e.symm hB
  have hFC := (ObjectProperty.triangEnvelope_le_iff _).mpr hgen _ hC
  rw [_root_.DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton A]
  apply P.prop_of_iso _ hFC
  exact ((ModuleCat.restrictScalars φ).mapDerivedCategorySingleFunctor 0).app
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of C C)) ≪≫
    (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).mapIso
      ((ModuleCat.restrictScalarsComp φ ψ).symm.app (ModuleCat.of C C))

/-- Exceptional coefficient mates compose with the canonical restriction compositors.
Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 1; Stacks 07A6
(blueprint: lem-route-perfect-coefficient-shriek-mate).
Proof: steps 8 and 9 of routePerfectCoefficientShriekMate. The two composites of the
scalar and exceptional adjunctions have the same left adjoints after the canonical scalar
associators. Conjugate the inverse of perfectCoefficientCompactSupportMap_comp. Conjugation
reverses composition and intertwines the scalar associators with the exact restriction
compositors. Evaluating the resulting natural-transformation equality at N yields exactly
the displayed equality, including both compositor factors. -/
theorem perfectCoefficientExceptionalIso_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (hB : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))))
    (hC : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} B) 0).obj
        ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of C C))))
    {FA : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
    {FB : DerivedCategoryModule B Y ⥤ DerivedCategoryModule B X}
    {FC : DerivedCategoryModule C Y ⥤ DerivedCategoryModule C X}
    (aA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ FA)
    (aB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ FB)
    (aC : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⊣ FC)
    (N : DerivedCategoryModule C Y) :
    (perfectCoefficientExceptionalIso (ψ.comp φ) f c
        (perfectCoefficientAlgebraComp φ ψ hB hC) aA aC).hom.app N =
      FA.map ((Sheaf.derivedRestrictScalarsCompIso Y.smallEtaleTopology
        (f := φ) (g := ψ) rfl).inv.app N) ≫
      (perfectCoefficientExceptionalIso φ f c hB aA aB).hom.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology ψ).obj N) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        ((perfectCoefficientExceptionalIso ψ f c hC aB aC).hom.app N) ≫
      (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
        (f := φ) (g := ψ) rfl).hom.app (FC.obj N) := by
  sorry

end AlgebraicGeometry.Etale
