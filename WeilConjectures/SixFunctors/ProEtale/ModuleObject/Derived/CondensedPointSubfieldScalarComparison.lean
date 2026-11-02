/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
public import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Connected.Separation
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WeakDimension
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
public import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients

/-! # Condensed point-section scalar comparison for finite subfields

Source: Hemo–Richarz–Scholbach, Lemma 4.1(1), specialized to a separably closed
geometric point (blueprint: lem-zl-condensed-point-subfield-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing


/-- Internal scalar extension at the point in the comparison.
Source: HRS Lemma 4.1(1)
(blueprint: lem-zl-condensed-point-subfield-scalar-comparison). -/
abbrev pointSubfieldExtension (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (k : Type u) [Field k] :=
  Mod.extendScalars
    (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) (Spec (.of k)))

end AlgebraicGeometry.ProEtale.CondensedRing
