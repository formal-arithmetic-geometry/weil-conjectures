/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModelReduction
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import Mathlib.RingTheory.Flat.Stability
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.SmoothPurity.ChangeOfRingsKFlatIndependentCoefficients

/-!
# Reduction of bounded flat models at finite coefficient levels

Source: Weil blueprint, sec-smooth-purity/sk-lem-sf-flat-model,
lem-sf-reduction-flat-model.md (blueprint: lem-sf-reduction-flat-model).

The pro-etale statement uses the recorded constant-ring module category and intrinsic
constructibility predicate. The etale statement uses the recorded finite-value
constructibility predicate.
All scalar extensions below use the canonical quotient map between the actual stages;
the upstream theorems provide the general proof ingredients without an encoding change.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep localization, tensor, and sheafification structures abstract during conversion.
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  SheafOfModules.monoidalCategory CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.presheafToSheaf CategoryTheory.sheafCompose
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  AlgebraicGeometry.Etale.derivedTensor
  AlgebraicGeometry.Etale.derivedTensorQObjSingleFunctorObjIso

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

section

attribute [local instance] SheafOfModules.KFlatFixedTensor.tensorAdditive
  SheafOfModules.KFlatFixedTensor.tensorObjAdditive
  SheafOfModules.KFlatFixedTensor.tensorHasMapBifunctor

end

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u})

/-- The quotient factor map between the actual finite coefficient rings, canonically
lifted to the coefficient universe. No flatness of this ring map is assumed.
Source: blueprint, lem-sf-reduction-flat-model.md, the map A_{E,n} to A_{E,m}
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionCoefficientMap :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E n) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E m) :=
  RingHom.ulift
    (Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal l E n)
      (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))

/-- The canonical constant coefficient map from stage n to stage m.
Source: blueprint, lem-sf-reduction-flat-model.md, coefficient reduction
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionRingMap :
    proEtaleConstantRing T (Padic.coefficientExtensionRing l E n) ⟶
      proEtaleConstantRing T (Padic.coefficientExtensionRing l E m) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (flatModelReductionCoefficientMap l E m n hmn))

/-- Canonical scalar extension with its specified object/map formulas and its universal
left-derived pair, specialized to the finite-level quotient map. The formulas determine
the ordinary functor; the universal property determines the derived pair up to unique
compatible isomorphism.
Source: Stacks Tags 03EK, 06YT and 06YY; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionData :=
  letI : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  letI : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  letI : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  letI := HasDerivedCategory.standard
    (proEtaleRingModules T (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)))
  letI := HasDerivedCategory.standard
    (proEtaleRingModules T (proEtaleConstantRing T (Padic.coefficientExtensionRing l E m)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (flatModelReductionRingMap l E m n hmn T)

/-- Ordinary tensor along the specified quotient map, fixed on objects and maps by
sectionwise tensor followed by sheafification in the recorded change-of-rings theorem.
Source: blueprint, lem-sf-reduction-flat-model.md, ordinary tensor complex
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionChange :=
  (flatModelReductionData l E m n hmn T).choose

/-- The universal left-derived scalar-extension pair and its K-flat computation.
Source: Stacks Tags 06YT and 06YY; blueprint, lem-sf-reduction-flat-model.md
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReductionDerivedData :=
  (flatModelReductionData l E m n hmn T).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived reduction from finite coefficient stage n to stage m, as the universal
left-derived functor of the specified ordinary scalar extension.
Source: blueprint, lem-sf-reduction-flat-model.md, definition of K_m
(blueprint: lem-sf-reduction-flat-model). -/
noncomputable def flatModelReduction :
    proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E m) :=
  (flatModelReductionDerivedData l E m n hmn T).choose

set_option linter.defProp false in
attribute [local irreducible] flatModelReductionData

set_option linter.defProp false in
attribute [local irreducible] flatModelReductionDerivedData

attribute [local irreducible] Functor.mapHomotopyCategory DerivedCategory.Qh DerivedCategory.Q
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

attribute [local irreducible] flatModelReductionChange flatModelReduction

end AlgebraicGeometry.Scheme

-- Use the same ring projection for generic rings and the lifted coefficient rings.
-- Otherwise conversion repeatedly normalizes the chosen coefficient subring.
attribute [local instance 2000] CommRing.toRing

namespace AlgebraicGeometry.Etale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n) (T : Scheme.{u})

end AlgebraicGeometry.Etale
