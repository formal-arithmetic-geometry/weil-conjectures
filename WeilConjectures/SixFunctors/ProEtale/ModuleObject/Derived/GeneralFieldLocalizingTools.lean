/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
public import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
public import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.Perfect

/-! # General-field localizing tools

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
  sk-thm-purity-transport.proof.md, coefficient transport Steps 1--4; general-field
  comparison is WANTED (blueprint: lem-dla1-general-field-localizing-tools).

The statement records the characteristic-free proper direct-image, Brown representability,
and open-immersion assertions for the native finite-extension and finite-subextension
condensed coefficient rings. All categories and functors are the existing ordinary
module-object derived categories and their recorded localizing closures.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Brown representability on the specified localizing closure, with its inherited
triangulated structure made explicit so that the functor's cohomological condition is
well-typed: every homological functor `L_Λ(S)ᵒᵖ ⥤ Ab` sending small coproducts of `L_Λ(S)`
to products is isomorphic to `Hom(-, G)` for an object `G` of `L_Λ(S)`. This is only an
interface for the localizing-closure assertion below; it chooses no additional category or
functor.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
sk-thm-purity-transport.proof.md, Steps 2-3, agent assembly of the general-field localizing
tools; the Brown clause of the node statement
(blueprint: lem-dla1-general-field-localizing-tools). -/
def BrownRepresentableOnLocalizingClosure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (H : (localizingClosureProEtale Λ S).FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : Prop :=
  ∃ hTri : (localizingClosureProEtale Λ S).IsTriangulated,
    letI := hTri
    ∀ [H.IsHomological],
      (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) H) →
        ∃ G : (localizingClosureProEtale Λ S).FullSubcategory,
          Nonempty (H ≅ preadditiveYoneda.obj G)

end AlgebraicGeometry.ProEtale.CondensedRing
