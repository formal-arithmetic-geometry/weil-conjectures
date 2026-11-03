/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
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
public import Mathlib.CategoryTheory.Adjunction.Additive
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.SixFunctors.Finite.Closed.FiniteClosedShriek
public import WeilConjectures.SixFunctors.Finite.FiniteDualizing
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointComparisons
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
public import WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
public import WeilConjectures.SixFunctors.Finite.FiniteVerdierCoefficientDiagrams
public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.Supporting.WeilVerdierPreservationStrata

/-! # Finite free coefficient extensions and cofinal levels

Source: Weil blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension; the unchanged statement is also in the master snapshot
(blueprint: def-sf-finite-free-coefficient-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.Etale.derivedTensor
  AlgebraicGeometry.Etale.derivedHom
  AlgebraicGeometry.ProEtale.derivedTensor AlgebraicGeometry.ProEtale.derivedHom
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- Functoriality of internal Hom in both arguments, with their endpoints shared explicitly.
Source: blueprint internal-Hom coefficient and geometric squares
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def homAction {C : Type w} [Category.{v} C] (H : Cᵒᵖ ⥤ C ⥤ C)
    {K K' M M' : C} (f : K' ⟶ K) (g : M ⟶ M') :
    ((H.obj (op K)).obj M) ⟶ ((H.obj (op K')).obj M') :=
  (H.map f.op).app M ≫ (H.obj (op K')).map g

/-- Stage categories use the recorded ordinary small etale category.
Source: blueprint finite-free coefficient change
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
abbrev Cat (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  Etale.DerivedCategoryModule A X

/-- Tensor-Hom adjunction in the published etale category.
Source: blueprint finite-free coefficient change
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
abbrev closed (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (K : Cat A X) :=
  Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K

/-- The fixed compactification determines the ambient exceptional functor.
Source: blueprint finite-free coefficient change
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def upper (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : Cat A S ⥤ Cat A X :=
  letI := c.hasCompactification
  Etale.rightDerivedUpperShriek A f

/-- The compact-support functor in the prescribed exceptional adjunction.
Source: blueprint finite-free coefficient change
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def support (A : Type (u + 1)) [CommRing A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : Cat A X ⥤ Cat A S :=
  letI := c.hasCompactification
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f

/-- The canonical exceptional adjunction for that same compactification.
Source: blueprint finite-free coefficient change
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def adj (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    support A c ⊣ upper A c :=
  letI := c.hasCompactification
  Etale.rightDerivedUpperShriekAdjunction A f

/-- The ordinary closed exceptional functor, fixed by the recorded right adjoint.
Source: blueprint closed-exceptional formula
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
abbrev closedUpper (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint

/-- The canonical closed-exceptional coefficient arrow, transposing the extended counit.
Source: blueprint closed-exceptional formula
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def closedMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Cat A X) :
    (Etale.scalarExtension φ Z).obj ((closedUpper A i).obj M) ⟶
      (closedUpper B i).obj ((Etale.scalarExtension φ X).obj M) :=
  (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))).homEquiv _ _
    ((open Classical in
      if h : IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj M))
      then @inv _ _ _ _ (Etale.finiteCoefficientDirectImageMap φ i
        ((closedUpper A i).obj M)) h else 0) ≫
      (Etale.scalarExtension φ X).map
        ((Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M))

/-- The dualizing object is the exceptional image of the regular coefficient unit.
Source: blueprint dualizing formula
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def omega (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : Cat A X :=
  (upper A c).obj (𝟙_ _)

/-- The canonical dualizing comparison, transposing the scalar compact-support counit.
Source: blueprint dualizing formula
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def omegaMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (Etale.scalarExtension φ X).obj (omega A c) ⟶ omega B c :=
  letI := c.hasCompactification
  Etale.ExceptionalCoefficients.mateMap φ f (𝟙_ _) ≫
    (upper B c).map (Etale.ExceptionalCoefficients.unitIso φ S).hom

/-- The internal-Hom comparison is the transpose of extended evaluation.
Source: blueprint internal-Hom formula
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def homMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K M : Cat A X) :
    (Etale.scalarExtension φ X).obj
        (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ⟶
      ((Etale.derivedHom (ModuleCat.{u + 1} B) X).obj
        (op ((Etale.scalarExtension φ X).obj K))).obj ((Etale.scalarExtension φ X).obj M) :=
  (closed B X ((Etale.scalarExtension φ X).obj K)).homEquiv _ _
    ((Etale.ExceptionalCoefficients.tensorIso φ X).inv.app
      (K, ((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ≫
        (Etale.scalarExtension φ X).map ((closed A X K).counit.app M))

/-- Verdier duality with the prescribed exceptional dualizing object.
Source: blueprint Verdier formula
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def dual (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :=
  (Etale.derivedHom (ModuleCat.{u + 1} A) X).flip.obj (omega A c)

/-- The Verdier comparison is Hom comparison followed by the dualizing comparison.
Source: blueprint Verdier formula
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def dualMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    (K : Cat A X) :
    (Etale.scalarExtension φ X).obj ((dual A c).obj (op K)) ⟶
      (dual B c).obj (op ((Etale.scalarExtension φ X).obj K)) :=
  homMap φ X K (omega A c) ≫
    ((Etale.derivedHom (ModuleCat.{u + 1} B) X).obj
      (op ((Etale.scalarExtension φ X).obj K))).map (omegaMap φ c)

/-- The finite-value bounded constructibility and ordered finite Tor interval of the node.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def Ctf (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    ObjectProperty (Cat A X) :=
  Etale.DerivedCategory.isBoundedConstructible A X ⊓ fun K ↦
    ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b K

/-- Canonical reassociation for arbitrary actual coefficient maps, including mixed squares.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
abbrev scalarComp {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ) (X : Scheme.{u}) :=
  ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h

namespace Sites

/-- The actual object type of the chosen small site.
Source: the two small sites in the coefficient lemma
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
@[reducible] def Site (pro : Bool) (X : Scheme.{u}) : Type (u + 1) :=
  match pro with
  | false => X.Etale
  | true => X.ProEt

/-- The existing category on the selected small site.
Source: the two small sites in the coefficient lemma
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
@[reducible] instance siteCategory (pro : Bool) (X : Scheme.{u}) : Category.{u} (Site pro X) := by
  cases pro <;> dsimp only [Site] <;> infer_instance

/-- The actual small-site topology.
Source: the two small sites in the coefficient lemma
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
@[reducible] def topology (pro : Bool) (X : Scheme.{u}) : GrothendieckTopology (Site pro X) := by
  cases pro
  · exact X.smallEtaleTopology
  · exact Scheme.ProEt.topology X

/-- The existing ordinary derived category for that site, with its native category instance.
Source: the two small sites in the coefficient lemma
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
abbrev D (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : Type (u + 2) :=
  DerivedCategory (Sheaf (topology pro X) (ModuleCat.{u + 1} A))

/-- The published derived tensor on the selected site.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def tensor (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    D pro A X ⥤ D pro A X ⥤ D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.derivedTensor (ModuleCat.{u + 1} A) X
  · exact ProEtale.derivedTensor (ModuleCat.{u + 1} A) X

/-- The published derived hom on the selected site.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def hom (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (D pro A X)ᵒᵖ ⥤ D pro A X ⥤ D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.derivedHom (ModuleCat.{u + 1} A) X
  · exact ProEtale.derivedHom (ModuleCat.{u + 1} A) X

/-- The published tensor-Hom adjunction, including its evaluation counit.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def adj (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (K : D pro A X) :
    (tensor pro A X).obj K ⊣ (hom pro A X).obj (op K) := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K
  · exact ProEtale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K

/-- The fixed derived coefficient extension on each actual small site.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def scalar (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) : D pro A X ⥤ D pro B X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.scalarExtension φ X
  · exact @ProEtale.pbcFixedScalarExtension.{u} X.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _ _ _ φ

/-- The exact site inverse image, with its existing derived localization.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def nu (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The ordinary derived site direct image.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def rnu (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor

/-- Scalar/site exchange in the shared stage categories, with its canonical endpoints.
Source: blueprint site comparison and coefficient squares
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def scalarSite {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    nu A X ⋙ scalar true φ X ≅ scalar false φ X ⋙ nu B X :=
  ProEtale.pbcComparisonReduction X φ

/-- The evaluation-defined site Hom arrow in the shared stage categories.
Source: blueprint site comparison and evaluation squares
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def siteHom (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K M : Cat A X) :
    (nu A X).obj (((hom false A X).obj (op K)).obj M) ⟶
      ((hom true A X).obj (op ((nu A X).obj K))).obj ((nu A X).obj M) :=
  ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M

/-- The two sites use their recorded finite-Tor constructible object properties.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def Ctf (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    ObjectProperty (D pro A X) := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact FiniteFreeCoefficients.Ctf A X
  · exact ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X

/-- Usual derived direct image on the selected site.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def push (pro : Bool) (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X) :
    D pro A T ⥤ D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact R(Etale.lowerStar (ModuleCat.{u + 1} A) f)
  · exact R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)

/-- The canonical projection comparison is the recorded counit-defined map.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def direct (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X) (K : D pro A T) :
    (scalar pro φ X).obj ((push pro A f).obj K) ⟶
      (push pro B f).obj ((scalar pro φ T).obj K) := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.finiteCoefficientDirectImageMap φ f K
  · exact ProEtale.finiteCoefficientChangeDirectImageMap φ f K

/-- The closed exceptional functor is ordinary etale, or its prescribed site transport.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def exceptional (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : D pro A X ⥤ D pro A Z := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact closedUpper A i
  · exact rnu A X ⋙ closedUpper A i ⋙ nu A Z

/-- The exceptional functor for a compactification and its site transport.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def upper (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : D pro A S ⥤ D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact FiniteFreeCoefficients.upper A c
  · exact rnu A S ⋙ FiniteFreeCoefficients.upper A c ⋙ nu A X

/-- The regular constant coefficient object in degree zero.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def one (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact 𝟙_ (Cat A X)
  · exact 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))

/-- The dualizing object is the prescribed exceptional inverse image of the base unit.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def omega (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : D pro A X :=
  (upper pro A c).obj (one pro A S)

/-- Verdier duality into that fixed object.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def dual (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (D pro A X)ᵒᵖ ⥤ D pro A X := (hom pro A X).flip.obj (omega pro A c)

/-- The type of coefficient tensorators; their ordinary balancing normalization is retained.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def TensorComparison (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :=
  Functor.uncurry.obj (tensor pro A X) ⋙ scalar pro φ X ≅
    (scalar pro φ X).prod (scalar pro φ X) ⋙ Functor.uncurry.obj (tensor pro B X)

/-- The transpose of scalar extension of the actual evaluation counit.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def homMap (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : TensorComparison pro φ X) (K M : D pro A X) :
    (scalar pro φ X).obj (((hom pro A X).obj (op K)).obj M) ⟶
      ((hom pro B X).obj (op ((scalar pro φ X).obj K))).obj ((scalar pro φ X).obj M) :=
  (adj pro B X ((scalar pro φ X).obj K)).homEquiv _ _
    (μ.inv.app (K, ((hom pro A X).obj (op K)).obj M) ≫
      (scalar pro φ X).map ((adj pro A X K).counit.app M))

/-- The Verdier map is the Hom map followed by the dualizing arrow.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def dualMap (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    (μ : TensorComparison pro φ X)
    (uMap : (scalar pro φ X).obj (omega pro A c) ⟶ omega pro B c) (K : D pro A X) :
    (scalar pro φ X).obj ((dual pro A c).obj (op K)) ⟶
      (dual pro B c).obj (op ((scalar pro φ X).obj K)) :=
  homMap pro φ X μ K (omega pro A c) ≫
    ((hom pro B X).obj (op ((scalar pro φ X).obj K))).map uMap

/-- Componentwise normalization by the descended pro-etale Koszul braiding.
Keeping the coefficient category abstract avoids reducing its derived monoidal instance.
Source: blueprint evaluation and double-dual compatibility
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def IsProKoszulSymmetry (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (b : ProEtale.derivedTensor A X ≅ (ProEtale.derivedTensor A X).flip) :
    Prop :=
  ∀ K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
    HEq ((b.hom.app K).app L)
      (DerivedMonoidal.braiding'
        (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology X) A))
        (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ)) K L).hom

/-- The signed symmetry is fixed componentwise by the published descended Koszul braiding.
Source: blueprint main-20261015, evaluation and double-dual compatibility
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def NormalizedSymmetry (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (b : tensor pro A X ≅ (tensor pro A X).flip) : Prop := by
  cases pro
  · exact Etale.IsEtaleKoszulSymmetry A X (fun K L ↦ (b.app K).app L)
  · exact IsProKoszulSymmetry (ModuleCat.{u + 1} A) X b

/-- Evaluation in dual-first order, using the same signed symmetry.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def evaluation (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (b : tensor pro A X ≅ (tensor pro A X).flip) (W K : D pro A X) :
    ((tensor pro A X).obj (((hom pro A X).obj (op K)).obj W)).obj K ⟶ W :=
  (b.hom.app (((hom pro A X).obj (op K)).obj W)).app K ≫
    (adj pro A X K).counit.app W

/-- The double-dual map is the transpose of the specified evaluation.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def bidual (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (b : tensor pro A X ≅ (tensor pro A X).flip) (W K : D pro A X) :
    K ⟶ ((hom pro A X).obj (op (((hom pro A X).obj (op K)).obj W))).obj W :=
  (adj pro A X (((hom pro A X).obj (op K)).obj W)).homEquiv _ _
    (evaluation pro A X b W K)

/-- The canonical scalar tensor associator, including mixed coefficient squares.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def comp (pro : Bool) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ) (X : Scheme.{u}) :
    scalar pro φ X ⋙ scalar pro ψ X ≅ scalar pro χ X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact scalarComp φ ψ χ h X
  · exact ProEtale.pbcFixedScalarExtensionComp.{u} (Scheme.ProEt.topology X) φ ψ χ h

/-- Normalization by the actual sheafified ordinary balancing on cochain representatives.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def NormalizedTensor (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : TensorComparison pro φ X) : Prop := by
  cases pro
  · exact HEq μ (Etale.ExceptionalCoefficients.tensorIso φ X)
  · letI := (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ).isLeftAdjoint
    exact ∃ δ,
      Etale.ExceptionalCoefficients.TensorNormalizationAux
        (finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ)
        (ProEtale.pbcFixedScalarExtension.{u} (Scheme.ProEt.topology X) φ)
        (finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ) δ ∧ HEq μ δ

/-- The closed exceptional site bridge is induced by the site-adjunction unit.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def closedBridge (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Cat A X) :
    (nu A Z).obj ((closedUpper A i).obj M) ⟶
      (exceptional true A i).obj ((nu A X).obj M) :=
  (nu A Z).map ((closedUpper A i).map
    ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app M))

/-- The dualizing site bridge is the exceptional image of the canonical base unit map.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def omegaBridge (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (nu A X).obj (FiniteFreeCoefficients.omega A c) ⟶ omega true A c :=
  (nu A X).map ((FiniteFreeCoefficients.upper A c).map
    (ProEtale.finiteDualityBaseUnit (ModuleCat.{u + 1} A) S
      (ProEtale.comparisonUpperStarUnitIso A S).hom))

/-- The canonical identity scalar extension, normalized by multiplication.
Source: blueprint identity coefficient maps (blueprint:
  def-sf-finite-free-coefficient-comparison-data). -/
def unit (pro : Bool) {A : Type (u + 1)} [CommRing A] (φ : A →+* A)
    (h : φ = RingHom.id A) (X : Scheme.{u}) : scalar pro φ X ≅ 𝟭 (D pro A X) := by
  cases pro
  · exact ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology φ h
  · exact ProEtale.normalizedOriginScalarUnit.{u} (Scheme.ProEt.topology X) φ h

attribute [local irreducible] tensor hom scalar push exceptional omega homMap dualMap
  evaluation bidual comp unit

/-- All five comparisons on one site, indexed by the actual field extensions and reductions.
The arrows not already defined above are characterized by the etale and site normalizations
below. In particular this structure does not replace a canonical arrow by an arbitrary map.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
structure Calculus (pro : Bool) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX) where
  symmetry : ∀ s : Stage l E, tensor pro s.ring X ≅ (tensor pro s.ring X).flip
  symmetry_normalized : ∀ s : Stage l E, NormalizedSymmetry pro s.ring X (symmetry s)
  tensorIso : ∀ {s t : Stage l E} (a : Arrow s t), TensorComparison pro a.ringMap X
  tensor_normalized : ∀ {s t : Stage l E} (a : Arrow s t),
    NormalizedTensor pro a.ringMap X (tensorIso a)
  closedMap : ∀ {s t : Stage l E} (a : Arrow s t) (M : D pro s.ring X),
    (scalar pro a.ringMap Z).obj ((exceptional pro s.ring i).obj M) ⟶
      (exceptional pro t.ring i).obj ((scalar pro a.ringMap X).obj M)
  omegaMap : ∀ {s t : Stage l E} (a : Arrow s t),
    (scalar pro a.ringMap X).obj (omega pro s.ring c) ⟶ omega pro t.ring c
  scalar_ctf_X : ∀ {s t : Stage l E} (a : Arrow s t) (K : D pro s.ring X),
    Ctf pro s.ring X K → Ctf pro t.ring X ((scalar pro a.ringMap X).obj K)
  scalar_ctf_T : ∀ {s t : Stage l E} (a : Arrow s t) (K : D pro s.ring T),
    Ctf pro s.ring T K → Ctf pro t.ring T ((scalar pro a.ringMap T).obj K)
  direct_iso : ∀ {s t : Stage l E} (a : Arrow s t) (K : D pro s.ring T),
    Ctf pro s.ring T K → IsIso (direct pro a.ringMap f K)
  closed_iso : ∀ {s t : Stage l E} (a : Arrow s t) (M : D pro s.ring X),
    Ctf pro s.ring X M → IsIso (closedMap a M)
  omega_iso : ∀ {s t : Stage l E} (a : Arrow s t), IsIso (omegaMap a)
  hom_iso : ∀ {s t : Stage l E} (a : Arrow s t) (K M : D pro s.ring X),
    Ctf pro s.ring X K → Ctf pro s.ring X M →
      IsIso (homMap pro a.ringMap X (tensorIso a) K M)
  dual_iso : ∀ {s t : Stage l E} (a : Arrow s t) (K : D pro s.ring X),
    Ctf pro s.ring X K → IsIso (dualMap pro a.ringMap c (tensorIso a) (omegaMap a) K)
  evaluation_eq : ∀ {s t : Stage l E} (a : Arrow s t) (K : D pro s.ring X),
    Ctf pro s.ring X K →
      ((tensor pro t.ring X).map
        (dualMap pro a.ringMap c (tensorIso a) (omegaMap a) K)).app
          ((scalar pro a.ringMap X).obj K) ≫
        evaluation pro t.ring X (symmetry t) (omega pro t.ring c) ((scalar pro a.ringMap X).obj K) =
      (tensorIso a).inv.app ((dual pro s.ring c).obj (op K), K) ≫
        (scalar pro a.ringMap X).map (evaluation pro s.ring X (symmetry s) (omega pro s.ring c) K) ≫
          omegaMap a
  bidual_eq : ∀ {s t : Stage l E} (a : Arrow s t) (K : D pro s.ring X),
    Ctf pro s.ring X K →
      (scalar pro a.ringMap X).map (bidual pro s.ring X (symmetry s) (omega pro s.ring c) K) ≫
        dualMap pro a.ringMap c (tensorIso a) (omegaMap a)
          ((dual pro s.ring c).obj (op K)) =
      bidual pro t.ring X (symmetry t) (omega pro t.ring c) ((scalar pro a.ringMap X).obj K) ≫
        (dual pro t.ring c).map
          (dualMap pro a.ringMap c (tensorIso a) (omegaMap a) K).op
  direct_natural : ∀ {s t : Stage l E} (a : Arrow s t) {K L : D pro s.ring T} (g : K ⟶ L),
    Ctf pro s.ring T K → Ctf pro s.ring T L →
      (scalar pro a.ringMap X).map ((push pro s.ring f).map g) ≫
        direct pro a.ringMap f L =
      direct pro a.ringMap f K ≫ (push pro t.ring f).map ((scalar pro a.ringMap T).map g)
  closed_natural : ∀ {s t : Stage l E} (a : Arrow s t) {K L : D pro s.ring X} (g : K ⟶ L),
    Ctf pro s.ring X K → Ctf pro s.ring X L →
      (scalar pro a.ringMap Z).map ((exceptional pro s.ring i).map g) ≫ closedMap a L =
      closedMap a K ≫ (exceptional pro t.ring i).map ((scalar pro a.ringMap X).map g)
  hom_natural : ∀ {s t : Stage l E} (a : Arrow s t)
      {K K' M M' : D pro s.ring X} (g : K' ⟶ K) (h : M ⟶ M'),
    Ctf pro s.ring X K → Ctf pro s.ring X K' →
    Ctf pro s.ring X M → Ctf pro s.ring X M' →
      (scalar pro a.ringMap X).map
        ((Functor.uncurry.obj (hom pro s.ring X)).map (Prod.mkHom g.op h)) ≫
          homMap pro a.ringMap X (tensorIso a) K' M' =
      homMap pro a.ringMap X (tensorIso a) K M ≫
        (Functor.uncurry.obj (hom pro t.ring X)).map
          (Prod.mkHom ((scalar pro a.ringMap X).map g).op ((scalar pro a.ringMap X).map h))
  dual_natural : ∀ {s t : Stage l E} (a : Arrow s t) {K L : D pro s.ring X} (g : K ⟶ L),
    Ctf pro s.ring X K → Ctf pro s.ring X L →
      (scalar pro a.ringMap X).map ((dual pro s.ring c).map g.op) ≫
        dualMap pro a.ringMap c (tensorIso a) (omegaMap a) K =
      dualMap pro a.ringMap c (tensorIso a) (omegaMap a) L ≫
        (dual pro t.ring c).map ((scalar pro a.ringMap X).map g).op
  direct_unit : ∀ (s : Stage l E) (a : Arrow s s)
      (h : a.embedding = AlgHom.id (Padic l) s.field) (K : D pro s.ring T),
    Ctf pro s.ring T K → direct pro a.ringMap f K ≫
      (push pro s.ring f).map ((unit pro a.ringMap (Arrow.ringMap_id a h) T).hom.app K) =
        (unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app ((push pro s.ring f).obj K)
  closed_unit : ∀ (s : Stage l E) (a : Arrow s s)
      (h : a.embedding = AlgHom.id (Padic l) s.field) (M : D pro s.ring X),
    Ctf pro s.ring X M → closedMap a M ≫
      (exceptional pro s.ring i).map ((unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app M) =
        (unit pro a.ringMap (Arrow.ringMap_id a h) Z).hom.app ((exceptional pro s.ring i).obj M)
  omega_unit : ∀ (s : Stage l E) (a : Arrow s s)
      (h : a.embedding = AlgHom.id (Padic l) s.field),
    omegaMap a = (unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app (omega pro s.ring c)
  hom_unit : ∀ (s : Stage l E) (a : Arrow s s)
      (h : a.embedding = AlgHom.id (Padic l) s.field) (K M : D pro s.ring X),
    Ctf pro s.ring X K → Ctf pro s.ring X M →
      homMap pro a.ringMap X (tensorIso a) K M ≫
        (Functor.uncurry.obj (hom pro s.ring X)).map
          (Prod.mkHom ((unit pro a.ringMap (Arrow.ringMap_id a h) X).inv.app K).op
            ((unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app M)) =
      (unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app
        (((hom pro s.ring X).obj (op K)).obj M)
  dual_unit : ∀ (s : Stage l E) (a : Arrow s s)
      (h : a.embedding = AlgHom.id (Padic l) s.field) (K : D pro s.ring X),
    Ctf pro s.ring X K → dualMap pro a.ringMap c (tensorIso a) (omegaMap a) K ≫
      (dual pro s.ring c).map ((unit pro a.ringMap (Arrow.ringMap_id a h) X).inv.app K).op =
        (unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app ((dual pro s.ring c).obj (op K))
  direct_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
      (h : ab.embedding = b.embedding.comp a.embedding) (K : D pro s.ring T),
    Ctf pro s.ring T K →
      (scalar pro b.ringMap X).map (direct pro a.ringMap f K) ≫
        direct pro b.ringMap f ((scalar pro a.ringMap T).obj K) ≫
          (push pro v.ring f).map
            ((comp pro a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h) T).hom.app K) =
      (comp pro a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h) X).hom.app
        ((push pro s.ring f).obj K) ≫ direct pro ab.ringMap f K
  closed_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
      (h : ab.embedding = b.embedding.comp a.embedding) (M : D pro s.ring X),
    Ctf pro s.ring X M →
      (scalar pro b.ringMap Z).map (closedMap a M) ≫
        closedMap b ((scalar pro a.ringMap X).obj M) ≫
          (exceptional pro v.ring i).map
            ((comp pro a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h) X).hom.app M) =
      (comp pro a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h) Z).hom.app
        ((exceptional pro s.ring i).obj M) ≫ closedMap ab M
  omega_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
      (h : ab.embedding = b.embedding.comp a.embedding),
    (scalar pro b.ringMap X).map (omegaMap a) ≫ omegaMap b =
      (comp pro a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h) X).hom.app
        (omega pro s.ring c) ≫ omegaMap ab
  hom_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
      (h : ab.embedding = b.embedding.comp a.embedding) (K M : D pro s.ring X),
    Ctf pro s.ring X K → Ctf pro s.ring X M →
      (comp pro a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h) X).hom.app
          (((hom pro s.ring X).obj (op K)).obj M) ≫
        homMap pro ab.ringMap X (tensorIso ab) K M =
      (scalar pro b.ringMap X).map (homMap pro a.ringMap X (tensorIso a) K M) ≫
        homMap pro b.ringMap X (tensorIso b)
          ((scalar pro a.ringMap X).obj K) ((scalar pro a.ringMap X).obj M) ≫
        (Functor.uncurry.obj (hom pro v.ring X)).map
          (Prod.mkHom
            ((comp pro a.ringMap b.ringMap ab.ringMap
              (Arrow.ringMap_comp a b ab h) X).inv.app K).op
            ((comp pro a.ringMap b.ringMap ab.ringMap
              (Arrow.ringMap_comp a b ab h) X).hom.app M))
  dual_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) (ab : Arrow s v)
      (h : ab.embedding = b.embedding.comp a.embedding) (K : D pro s.ring X),
    Ctf pro s.ring X K →
      (scalar pro b.ringMap X).map
          (dualMap pro a.ringMap c (tensorIso a) (omegaMap a) K) ≫
        dualMap pro b.ringMap c (tensorIso b) (omegaMap b) ((scalar pro a.ringMap X).obj K) ≫
          (dual pro v.ring c).map
            ((comp pro a.ringMap b.ringMap ab.ringMap
              (Arrow.ringMap_comp a b ab h) X).inv.app K).op =
      (comp pro a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h) X).hom.app
        ((dual pro s.ring c).obj (op K)) ≫
          dualMap pro ab.ringMap c (tensorIso ab) (omegaMap ab) K

attribute [local semireducible] tensor hom scalar push exceptional omega homMap dualMap
  evaluation bidual comp unit

/-- The canonical Verdier site arrow is the evaluation-defined Hom arrow followed by
the prescribed dualizing site arrow.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def dualBridge (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) (K : Cat A X) :
    (nu A X).obj ((FiniteFreeCoefficients.dual A c).obj (op K)) ⟶
      (dual true A c).obj (op ((nu A X).obj K)) :=
  siteHom A X K
      (FiniteFreeCoefficients.omega A c) ≫
    ((hom true A X).obj (op ((nu A X).obj K))).map (omegaBridge A c)

/-- The ordinary etale arrows are fixed by their counit and evaluation definitions;
the pro-etale arrows are fixed by the canonical site-comparison squares. These equations
retain the precise etale/pro-etale realizations, rather than merely asserting existence
of isomorphisms between abstract endpoint objects.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: def-sf-finite-free-coefficient-comparison-data). -/
structure NormalizedAux (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (et : Calculus false l E f i c) (pro : Calculus true l E f i c)
    [HasCompactification aX] : Prop where
  etale_closed : ∀ {s t : Stage l E} (a : Arrow s t) (M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X M →
      et.closedMap a M = FiniteFreeCoefficients.closedMap a.ringMap i M
  etale_omega : ∀ {s t : Stage l E} (a : Arrow s t),
    et.omegaMap a = FiniteFreeCoefficients.omegaMap a.ringMap c
  compact_support_iso : ∀ {s t : Stage l E} (a : Arrow s t),
    IsIso (Etale.ExceptionalCoefficients.compactSupportMap a.ringMap
      (HasCompactification.compactification aX)
      (FiniteFreeCoefficients.omega s.ring c))
  closed_direct_iso : ∀ {s t : Stage l E} (a : Arrow s t) (M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X M →
      IsIso (Etale.finiteCoefficientDirectImageMap a.ringMap i ((closedUpper s.ring i).obj M))
  closed_counit : ∀ {s t : Stage l E} (a : Arrow s t) (M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X M →
      Etale.finiteCoefficientDirectImageMap a.ringMap i ((closedUpper s.ring i).obj M) ≫
        (R(Etale.lowerStar (ModuleCat.{u + 1} t.ring) i)).map (et.closedMap a M) ≫
        (Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} t.ring) i))).counit.app
            ((Etale.scalarExtension a.ringMap X).obj M) =
      (Etale.scalarExtension a.ringMap X).map
        ((Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} s.ring) i))).counit.app M)
  omega_counit : ∀ {s t : Stage l E} (a : Arrow s t),
    (support t.ring c).map (et.omegaMap a) ≫ (FiniteFreeCoefficients.adj t.ring c).counit.app
        (𝟙_ _) =
      Etale.ExceptionalCoefficients.comparisonInverse a.ringMap
          (HasCompactification.compactification aX)
          (FiniteFreeCoefficients.omega s.ring c) ≫
        (Etale.scalarExtension a.ringMap S).map
          ((FiniteFreeCoefficients.adj s.ring c).counit.app (𝟙_ _)) ≫
        (Etale.ExceptionalCoefficients.unitIso a.ringMap S).hom
  closed_site_iso : ∀ (s : Stage l E) (M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X M → IsIso (closedBridge s.ring i M)
  omega_site_iso : ∀ s : Stage l E, IsIso (omegaBridge s.ring c)
  hom_site_iso : ∀ (s : Stage l E) (K M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X K → FiniteFreeCoefficients.Ctf s.ring X M →
      IsIso (siteHom s.ring X K M)
  dual_site_iso : ∀ (s : Stage l E) (K : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X K → IsIso (dualBridge s.ring c K)
  closed_site : ∀ {s t : Stage l E} (a : Arrow s t) (M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X M →
      (scalar true a.ringMap Z).map (closedBridge s.ring i M) ≫
        pro.closedMap a ((nu s.ring X).obj M) ≫
          (exceptional true t.ring i).map ((scalarSite a.ringMap X).hom.app M) =
      (scalarSite a.ringMap Z).hom.app ((closedUpper s.ring i).obj M) ≫
        (nu t.ring Z).map (et.closedMap a M) ≫
          closedBridge t.ring i ((Etale.scalarExtension a.ringMap X).obj M)
  omega_site : ∀ {s t : Stage l E} (a : Arrow s t),
    (scalar true a.ringMap X).map (omegaBridge s.ring c) ≫ pro.omegaMap a =
      (scalarSite a.ringMap X).hom.app
          (FiniteFreeCoefficients.omega s.ring c) ≫
        (nu t.ring X).map (et.omegaMap a) ≫ omegaBridge t.ring c
  hom_site : ∀ {s t : Stage l E} (a : Arrow s t) (K M : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X K → FiniteFreeCoefficients.Ctf s.ring X M →
      (scalar true a.ringMap X).map
          (siteHom s.ring X K M) ≫
        homMap true a.ringMap X (pro.tensorIso a) ((nu s.ring X).obj K) ((nu s.ring X).obj M) ≫
        homAction (hom true t.ring X)
          ((scalarSite a.ringMap X).inv.app K)
          ((scalarSite a.ringMap X).hom.app M) =
      (scalarSite a.ringMap X).hom.app
          (((hom false s.ring X).obj (op K)).obj M) ≫
        (nu t.ring X).map (homMap false a.ringMap X (et.tensorIso a) K M) ≫
        siteHom t.ring X
          ((Etale.scalarExtension a.ringMap X).obj K) ((Etale.scalarExtension a.ringMap X).obj M)
  dual_site : ∀ {s t : Stage l E} (a : Arrow s t) (K : Cat s.ring X),
    FiniteFreeCoefficients.Ctf s.ring X K →
      (scalar true a.ringMap X).map (dualBridge s.ring c K) ≫
        dualMap true a.ringMap c (pro.tensorIso a) (pro.omegaMap a) ((nu s.ring X).obj K) ≫
        (dual true t.ring c).map
          ((scalarSite a.ringMap X).inv.app K).op =
      (scalarSite a.ringMap X).hom.app
          ((FiniteFreeCoefficients.dual s.ring c).obj (op K)) ≫
        (nu t.ring X).map (dualMap false a.ringMap c (et.tensorIso a) (et.omegaMap a) K) ≫
        dualBridge t.ring c ((Etale.scalarExtension a.ringMap X).obj K)

/-- The same counit and site normalizations, with compactifiability supplied by c.
Source: blueprint canonical coefficient comparisons
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def Normalized (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (et : Calculus false l E f i c) (pro : Calculus true l E f i c) : Prop :=
  letI := c.hasCompactification
  NormalizedAux l E f i c et pro

/-- The actual ordinary etale inverse image.
Source: blueprint main-20261015, lem-coef-finite-free-extension, scheme-isomorphism
naturality, including geometric Frobenius (blueprint:
  def-sf-finite-free-coefficient-comparison-data). -/
def pull (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X) :=
  L(Etale.upperStar (ModuleCat.{u + 1} A) g)

/-- Scalar/geometric exchange in the same categories used by the Hom square.
Source: blueprint geometric coefficient squares
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def scalarPull {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Y X : Scheme.{u}} (g : Y ⟶ X) :
    Etale.scalarExtension φ X ⋙ pull B g ≅ pull A g ⋙ Etale.scalarExtension φ Y :=
  Etale.scalarPullbackIso φ g

/-- The canonical geometric Hom comparison is the transpose of pulled-back evaluation.
Source: blueprint main-20261015, lem-coef-finite-free-extension, scheme-isomorphism
naturality, including geometric Frobenius (blueprint:
  def-sf-finite-free-coefficient-comparison-data). -/
def pullHom (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X)
    (K M : Cat A X) :
    (pull A g).obj (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ⟶
      ((Etale.derivedHom (ModuleCat.{u + 1} A) Y).obj (op ((pull A g).obj K))).obj
        ((pull A g).obj M) :=
  (FiniteFreeCoefficients.closed A Y ((pull A g).obj K)).homEquiv _ _
    ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K
      (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).inv ≫
      (pull A g).map ((FiniteFreeCoefficients.closed A X K).counit.app M))

/-- The exceptional coefficient mate commutes with isomorphism base change.
At a closed immersion this is the unique closed counit mate; at the structure morphism
and the unit it is precisely dualizing naturality. Verdier naturality is their composite
with HomGeometry. The base is allowed to move, as required for geometric Frobenius.
Source: blueprint main-20261015, lem-coef-finite-free-extension, scheme-isomorphism
naturality, including geometric Frobenius (blueprint:
  def-sf-finite-free-coefficient-comparison-data). -/
def ExceptionalGeometry {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S}
    [QuasiCompact f] (c : Compactification f) (M : Cat A S) : Prop :=
  letI := c.hasCompactification
  ∀ (S' : Scheme.{u}) (e : S' ≅ S),
    Etale.ExceptionalCoefficients.BaseChangeCompatibility φ f e.hom M

/-- Inverse on the isomorphism domain, extended by zero elsewhere.
Source: blueprint finite constructible comparison domains
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def inverseOnDomain {C : Type w} [Category.{v} C] [Preadditive C]
    {K M : C} (b : K ⟶ M) : M ⟶ K :=
  open Classical in
  if h : IsIso b then @inv _ _ _ _ b h else 0

/-- Actual pro-etale inverse image used by scheme-isomorphism naturality.
Source: blueprint geometric coefficient squares
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def proPull (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X) :=
  L(ProEtale.upperStar (ModuleCat.{u + 1} A) g)

/-- Canonical derived scalar/pullback comparison from the restriction/direct-image identity.
Source: blueprint geometric coefficient squares and the fixed scalar adjunctions
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def proScalarPull {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y X : Scheme.{u}} (g : Y ⟶ X) :
    scalar true φ X ⋙ proPull B g ≅ proPull A g ⋙ scalar true φ Y :=
  (conjugateIsoEquiv
    ((ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)))
    ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)).comp
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g))).symm
    (ProEtale.fixedScalarRestrictionDirectImage φ g)

/-- Exact inverse image commutes with the comparison pullback by the canonical site square.
Source: blueprint site transport of geometric diagrams
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def sitePull (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X) :
    nu A X ⋙ proPull A g ≅ pull A g ⋙ nu A Y :=
  Functor.isoWhiskerLeft _
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g) ≪≫
    Functor.mapDerivedCategorySquareIso
      (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g) ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).symm _

/-- The site-direct-image/scalar mate is the comparison-pullback transpose.
Source: blueprint site transport of coefficient counits
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def rnuScalar {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (M : D true A X) :
    (scalar false φ X).obj ((rnu A X).obj M) ⟶
      (rnu B X).obj ((scalar true φ X).obj M) :=
  (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) X).homEquiv _ _
    ((scalarSite φ X).inv.app ((rnu A X).obj M) ≫
      (scalar true φ X).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app M))

/-- The mate of the site/geometric square, retaining its ordinary comparison counit.
Source: blueprint geometric site transport
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def rnuPull (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X)
    (M : D true A X) :
    (pull A g).obj ((rnu A X).obj M) ⟶ (rnu A Y).obj ((proPull A g).obj M) :=
  (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ _
    ((sitePull A g).inv.app ((rnu A X).obj M) ≫
      (proPull A g).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app M))

/-- Canonical closed coefficient map on the pro-etale transported exceptional functor.
Source: blueprint transported closed-exceptional comparison, with the site counit mate
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def proClosedMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : D true A X) :
    (scalar true φ Z).obj ((exceptional true A i).obj M) ⟶
      (exceptional true B i).obj ((scalar true φ X).obj M) :=
  (scalarSite φ Z).hom.app ((closedUpper A i).obj ((rnu A X).obj M)) ≫
    (nu B Z).map (FiniteFreeCoefficients.closedMap φ i ((rnu A X).obj M)) ≫
    (nu B Z).map ((closedUpper B i).map (rnuScalar φ X M))

/-- Base change for the actual etale closed right adjoint, transposing its own counit.
This uses direct image rather than the compact-support adjunction at a proper compactification.
Source: blueprint closed-exceptional geometric naturality
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def closedPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (g : Y ⟶ X) (M : Cat A X) :
    (pull A (pullback.fst i g)).obj ((closedUpper A i).obj M) ⟶
      (closedUpper A (pullback.snd i g)).obj ((pull A g).obj M) :=
  (Adjunction.ofIsLeftAdjoint
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) (pullback.snd i g)))).homEquiv _ _
    (inverseOnDomain ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback i g).toCommSq).app ((closedUpper A i).obj M)) ≫
      (pull A g).map
        ((Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M))

/-- The pro-etale dualizing coefficient map in canonical site coordinates.
Source: blueprint dualizing site square
(blueprint: def-sf-finite-free-coefficient-comparison-data). -/
def proOmegaMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (scalar true φ X).obj (omega true A c) ⟶ omega true B c :=
  (scalar true φ X).map (inverseOnDomain (omegaBridge A c)) ≫
    (scalarSite φ X).hom.app (FiniteFreeCoefficients.omega A c) ≫
    (nu B X).map (FiniteFreeCoefficients.omegaMap φ c) ≫ omegaBridge B c

end Sites

end WeilConjectures.FiniteFreeCoefficients
