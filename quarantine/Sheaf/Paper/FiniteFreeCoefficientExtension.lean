/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.DualityPairing
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.SixFunctors.FiniteDualitySiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.FiniteClosedShriek
public import Sheaf.SixFunctors.FiniteDualizing
public import Sheaf.Paper.FiniteCoefficientHomChange
public import Sheaf.SixFunctors.FiniteCoefficientVerdier
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.FiniteCoefficientAdjointComparisons
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison
public import Sheaf.Paper.ExceptionalCoefficientComparison
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.EtaleUnboundedRestrictionComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange
import Sheaf.Paper.WeilVerdierPreservationStrata
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.FiniteEtaleDescent
import Sheaf.CategoryTheory.AdjointMate
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-! # Finite free coefficient extensions and cofinal levels

Source: Weil blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension; the unchanged statement is also in the master snapshot
(blueprint: lem-coef-finite-free-extension).
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
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- Functoriality of internal Hom in both arguments, with their endpoints shared explicitly.
Source: blueprint internal-Hom coefficient and geometric squares
(blueprint: lem-coef-finite-free-extension). -/
def homAction {C : Type w} [Category.{v} C] (H : Cᵒᵖ ⥤ C ⥤ C)
    {K K' M M' : C} (f : K' ⟶ K) (g : M ⟶ M') :
    ((H.obj (op K)).obj M) ⟶ ((H.obj (op K')).obj M') :=
  (H.map f.op).app M ≫ (H.obj (op K')).map g

/-- Stage categories use the recorded ordinary small etale category.
Source: blueprint finite-free coefficient change
(blueprint: lem-coef-finite-free-extension). -/
abbrev Cat (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  Etale.DerivedCategoryModule A X

/-- Tensor-Hom adjunction in the published etale category.
Source: blueprint finite-free coefficient change
(blueprint: lem-coef-finite-free-extension). -/
abbrev closed (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (K : Cat A X) :=
  Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K

/-- The fixed compactification determines the ambient exceptional functor.
Source: blueprint finite-free coefficient change
(blueprint: lem-coef-finite-free-extension). -/
def upper (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : Cat A S ⥤ Cat A X :=
  letI := c.hasCompactification
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f

/-- The compact-support functor in the prescribed exceptional adjunction.
Source: blueprint finite-free coefficient change
(blueprint: lem-coef-finite-free-extension). -/
def support (A : Type (u + 1)) [CommRing A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : Cat A X ⥤ Cat A S :=
  letI := c.hasCompactification
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f

/-- The canonical exceptional adjunction for that same compactification.
Source: blueprint finite-free coefficient change
(blueprint: lem-coef-finite-free-extension). -/
def adj (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    support A c ⊣ upper A c :=
  letI := c.hasCompactification
  Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f

/-- The ordinary closed exceptional functor, fixed by the recorded right adjoint.
Source: blueprint closed-exceptional formula
(blueprint: lem-coef-finite-free-extension). -/
abbrev closedUpper (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint

/-- The canonical closed-exceptional coefficient arrow, transposing the extended counit.
Source: blueprint closed-exceptional formula
(blueprint: lem-coef-finite-free-extension). -/
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
(blueprint: lem-coef-finite-free-extension). -/
def omega (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : Cat A X :=
  (upper A c).obj (𝟙_ _)

/-- The canonical dualizing comparison, transposing the scalar compact-support counit.
Source: blueprint dualizing formula
(blueprint: lem-coef-finite-free-extension). -/
def omegaMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (Etale.scalarExtension φ X).obj (omega A c) ⟶ omega B c :=
  letI := c.hasCompactification
  Etale.ExceptionalCoefficients.mateMap φ f (𝟙_ _) ≫
    (upper B c).map (Etale.ExceptionalCoefficients.unitIso φ S).hom

/-- The internal-Hom comparison is the transpose of extended evaluation.
Source: blueprint internal-Hom formula
(blueprint: lem-coef-finite-free-extension). -/
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
(blueprint: lem-coef-finite-free-extension). -/
def dual (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :=
  (Etale.derivedHom (ModuleCat.{u + 1} A) X).flip.obj (omega A c)

/-- The Verdier comparison is Hom comparison followed by the dualizing comparison.
Source: blueprint Verdier formula
(blueprint: lem-coef-finite-free-extension). -/
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
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def Ctf (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    ObjectProperty (Cat A X) :=
  Etale.DerivedCategory.isBoundedConstructible A X ⊓ fun K ↦
    ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b K

/-- Canonical reassociation for arbitrary actual coefficient maps, including mixed squares.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
abbrev scalarComp {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ) (X : Scheme.{u}) :=
  ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h

namespace Sites

/-- The actual object type of the chosen small site.
Source: the two small sites in the coefficient lemma
(blueprint: lem-coef-finite-free-extension). -/
@[reducible] def Site (pro : Bool) (X : Scheme.{u}) : Type (u + 1) :=
  match pro with
  | false => X.Etale
  | true => X.ProEt

/-- The existing category on the selected small site.
Source: the two small sites in the coefficient lemma
(blueprint: lem-coef-finite-free-extension). -/
@[reducible] instance siteCategory (pro : Bool) (X : Scheme.{u}) : Category.{u} (Site pro X) := by
  cases pro <;> dsimp only [Site] <;> infer_instance

/-- The actual small-site topology.
Source: the two small sites in the coefficient lemma
(blueprint: lem-coef-finite-free-extension). -/
@[reducible] def topology (pro : Bool) (X : Scheme.{u}) : GrothendieckTopology (Site pro X) := by
  cases pro
  · exact X.smallEtaleTopology
  · exact Scheme.ProEt.topology X

/-- The existing ordinary derived category for that site, with its native category instance.
Source: the two small sites in the coefficient lemma
(blueprint: lem-coef-finite-free-extension). -/
abbrev D (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : Type (u + 2) :=
  DerivedCategory (Sheaf (topology pro X) (ModuleCat.{u + 1} A))

/-- The published derived tensor on the selected site.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def tensor (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    D pro A X ⥤ D pro A X ⥤ D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.derivedTensor (ModuleCat.{u + 1} A) X
  · exact ProEtale.derivedTensor (ModuleCat.{u + 1} A) X

/-- The published derived hom on the selected site.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def hom (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (D pro A X)ᵒᵖ ⥤ D pro A X ⥤ D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.derivedHom (ModuleCat.{u + 1} A) X
  · exact ProEtale.derivedHom (ModuleCat.{u + 1} A) X

/-- The published tensor-Hom adjunction, including its evaluation counit.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def adj (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (K : D pro A X) :
    (tensor pro A X).obj K ⊣ (hom pro A X).obj (op K) := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K
  · exact ProEtale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K

/-- The fixed derived coefficient extension on each actual small site.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def scalar (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) : D pro A X ⥤ D pro B X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.scalarExtension φ X
  · exact @ProEtale.pbcFixedScalarExtension.{u} X.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) _ _ _ _ φ

/-- The exact site inverse image, with its existing derived localization.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def nu (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The ordinary derived site direct image.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def rnu (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor

/-- Scalar/site exchange in the shared stage categories, with its canonical endpoints.
Source: blueprint site comparison and coefficient squares
(blueprint: lem-coef-finite-free-extension). -/
def scalarSite {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    nu A X ⋙ scalar true φ X ≅ scalar false φ X ⋙ nu B X :=
  ProEtale.pbcComparisonReduction X φ

/-- The evaluation-defined site Hom arrow in the shared stage categories.
Source: blueprint site comparison and evaluation squares
(blueprint: lem-coef-finite-free-extension). -/
def siteHom (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K M : Cat A X) :
    (nu A X).obj (((hom false A X).obj (op K)).obj M) ⟶
      ((hom true A X).obj (op ((nu A X).obj K))).obj ((nu A X).obj M) :=
  ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M

/-- The two sites use their recorded finite-Tor constructible object properties.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def Ctf (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    ObjectProperty (D pro A X) := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact FiniteFreeCoefficients.Ctf A X
  · exact ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X

/-- Usual derived direct image on the selected site.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def push (pro : Bool) (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X) :
    D pro A T ⥤ D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact R(Etale.lowerStar (ModuleCat.{u + 1} A) f)
  · exact R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)

/-- The canonical projection comparison is the recorded counit-defined map.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def direct (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X) (K : D pro A T) :
    (scalar pro φ X).obj ((push pro A f).obj K) ⟶
      (push pro B f).obj ((scalar pro φ T).obj K) := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact Etale.finiteCoefficientDirectImageMap φ f K
  · exact ProEtale.finiteCoefficientChangeDirectImageMap φ f K

/-- The closed exceptional functor is ordinary etale, or its prescribed site transport.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def exceptional (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : D pro A X ⥤ D pro A Z := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact closedUpper A i
  · exact rnu A X ⋙ closedUpper A i ⋙ nu A Z

/-- The exceptional functor for a compactification and its site transport.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def upper (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : D pro A S ⥤ D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact FiniteFreeCoefficients.upper A c
  · exact rnu A S ⋙ FiniteFreeCoefficients.upper A c ⋙ nu A X

/-- The regular constant coefficient object in degree zero.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def one (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) : D pro A X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact 𝟙_ (Cat A X)
  · exact 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))

/-- The dualizing object is the prescribed exceptional inverse image of the base unit.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def omega (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) : D pro A X :=
  (upper pro A c).obj (one pro A S)

/-- Verdier duality into that fixed object.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def dual (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (D pro A X)ᵒᵖ ⥤ D pro A X := (hom pro A X).flip.obj (omega pro A c)

/-- The type of coefficient tensorators; their ordinary balancing normalization is retained.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def TensorComparison (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :=
  Functor.uncurry.obj (tensor pro A X) ⋙ scalar pro φ X ≅
    (scalar pro φ X).prod (scalar pro φ X) ⋙ Functor.uncurry.obj (tensor pro B X)

/-- The transpose of scalar extension of the actual evaluation counit.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def homMap (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : TensorComparison pro φ X) (K M : D pro A X) :
    (scalar pro φ X).obj (((hom pro A X).obj (op K)).obj M) ⟶
      ((hom pro B X).obj (op ((scalar pro φ X).obj K))).obj ((scalar pro φ X).obj M) :=
  (adj pro B X ((scalar pro φ X).obj K)).homEquiv _ _
    (μ.inv.app (K, ((hom pro A X).obj (op K)).obj M) ≫
      (scalar pro φ X).map ((adj pro A X K).counit.app M))

/-- The Verdier map is the Hom map followed by the dualizing arrow.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
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
(blueprint: lem-coef-finite-free-extension). -/
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
(blueprint: lem-coef-finite-free-extension). -/
def NormalizedSymmetry (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (b : tensor pro A X ≅ (tensor pro A X).flip) : Prop := by
  cases pro
  · exact Etale.IsEtaleKoszulSymmetry A X (fun K L ↦ (b.app K).app L)
  · exact IsProKoszulSymmetry (ModuleCat.{u + 1} A) X b

/-- Evaluation in dual-first order, using the same signed symmetry.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def evaluation (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (b : tensor pro A X ≅ (tensor pro A X).flip) (W K : D pro A X) :
    ((tensor pro A X).obj (((hom pro A X).obj (op K)).obj W)).obj K ⟶ W :=
  (b.hom.app (((hom pro A X).obj (op K)).obj W)).app K ≫
    (adj pro A X K).counit.app W


/-- The double-dual map is the transpose of the specified evaluation.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def bidual (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (b : tensor pro A X ≅ (tensor pro A X).flip) (W K : D pro A X) :
    K ⟶ ((hom pro A X).obj (op (((hom pro A X).obj (op K)).obj W))).obj W :=
  (adj pro A X (((hom pro A X).obj (op K)).obj W)).homEquiv _ _
    (evaluation pro A X b W K)


/-- The canonical scalar tensor associator, including mixed coefficient squares.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def comp (pro : Bool) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ) (X : Scheme.{u}) :
    scalar pro φ X ⋙ scalar pro ψ X ≅ scalar pro χ X := by
  cases pro <;> dsimp only [D, topology, Site] at *
  · exact scalarComp φ ψ χ h X
  · exact ProEtale.pbcFixedScalarExtensionComp.{u} (Scheme.ProEt.topology X) φ ψ χ h


/-- Normalization by the actual sheafified ordinary balancing on cochain representatives.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
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
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def closedBridge (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Cat A X) :
    (nu A Z).obj ((closedUpper A i).obj M) ⟶
      (exceptional true A i).obj ((nu A X).obj M) :=
  (nu A Z).map ((closedUpper A i).map
    ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app M))


/-- The dualizing site bridge is the exceptional image of the canonical base unit map.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
def omegaBridge (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (nu A X).obj (FiniteFreeCoefficients.omega A c) ⟶ omega true A c :=
  (nu A X).map ((FiniteFreeCoefficients.upper A c).map
    (ProEtale.finiteDualityBaseUnit (ModuleCat.{u + 1} A) S
      (ProEtale.comparisonUpperStarUnitIso A S).hom))



/-- The canonical identity scalar extension, normalized by multiplication.
Source: blueprint identity coefficient maps (blueprint: lem-coef-finite-free-extension). -/
def unit (pro : Bool) {A : Type (u + 1)} [CommRing A] (φ : A →+* A)
    (h : φ = RingHom.id A) (X : Scheme.{u}) : scalar pro φ X ≅ 𝟭 (D pro A X) := by
  cases pro
  · exact ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology φ h
  · exact ProEtale.normalizedOriginScalarUnit.{u} (Scheme.ProEt.topology X) φ h


/-- All five comparisons on one site, indexed by the actual field extensions and reductions.
The arrows not already defined above are characterized by the etale and site normalizations
below. In particular this structure does not replace a canonical arrow by an arbitrary map.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
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



/-- The canonical Verdier site arrow is the evaluation-defined Hom arrow followed by
the prescribed dualizing site arrow.
Source: blueprint main-20261015, lem-coef-finite-free-extension, displayed comparisons
and their coherence (blueprint: lem-coef-finite-free-extension). -/
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
and their coherence (blueprint: lem-coef-finite-free-extension). -/
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
(blueprint: lem-coef-finite-free-extension). -/
def Normalized (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (et : Calculus false l E f i c) (pro : Calculus true l E f i c) : Prop :=
  letI := c.hasCompactification
  NormalizedAux l E f i c et pro

/-- The actual ordinary etale inverse image.
Source: blueprint main-20261015, lem-coef-finite-free-extension, scheme-isomorphism
naturality, including geometric Frobenius (blueprint: lem-coef-finite-free-extension). -/
def pull (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X) :=
  L(Etale.upperStar (ModuleCat.{u + 1} A) g)


/-- Scalar/geometric exchange in the same categories used by the Hom square.
Source: blueprint geometric coefficient squares
(blueprint: lem-coef-finite-free-extension). -/
def scalarPull {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Y X : Scheme.{u}} (g : Y ⟶ X) :
    Etale.scalarExtension φ X ⋙ pull B g ≅ pull A g ⋙ Etale.scalarExtension φ Y :=
  Etale.scalarPullbackIso φ g

/-- The canonical geometric Hom comparison is the transpose of pulled-back evaluation.
Source: blueprint main-20261015, lem-coef-finite-free-extension, scheme-isomorphism
naturality, including geometric Frobenius (blueprint: lem-coef-finite-free-extension). -/
def pullHom (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X)
    (K M : Cat A X) :
    (pull A g).obj (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ⟶
      ((Etale.derivedHom (ModuleCat.{u + 1} A) Y).obj (op ((pull A g).obj K))).obj
        ((pull A g).obj M) :=
  (FiniteFreeCoefficients.closed A Y ((pull A g).obj K)).homEquiv _ _
    ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K
      (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).inv ≫
      (pull A g).map ((FiniteFreeCoefficients.closed A X K).counit.app M))


/-- The direct-image square under the canonical pullback by a scheme isomorphism.
Source: blueprint main-20261015, lem-coef-finite-free-extension, scheme-isomorphism
naturality, including geometric Frobenius (blueprint: lem-coef-finite-free-extension). -/
def DirectGeometry {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X) : Prop :=
  ∀ (Y : Scheme.{u}) (e : Y ≅ X) (K : Cat A T), FiniteFreeCoefficients.Ctf A T K →
    (Etale.scalarExtension φ Y).map
        ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback f e.hom).toCommSq).app K) ≫
      Etale.finiteCoefficientDirectImageMap φ (pullback.snd f e.hom)
        ((pull A (pullback.fst f e.hom)).obj K) ≫
      (R(Etale.lowerStar (ModuleCat.{u + 1} B) (pullback.snd f e.hom))).map
        ((Etale.scalarPullbackIso φ (pullback.fst f e.hom)).inv.app K) =
    (scalarPull φ e.hom).inv.app
        ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
      (pull B e.hom).map (Etale.finiteCoefficientDirectImageMap φ f K) ≫
      (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} B)
        (IsPullback.of_hasPullback f e.hom).toCommSq).app ((Etale.scalarExtension φ T).obj K)


/-- The coefficient and geometric Hom transposes commute under every scheme isomorphism.
Source: blueprint main-20261015, lem-coef-finite-free-extension, scheme-isomorphism
naturality, including geometric Frobenius (blueprint: lem-coef-finite-free-extension). -/
def HomGeometry {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) (X : Scheme.{u}) : Prop :=
  ∀ (Y : Scheme.{u}) (e : Y ≅ X) (K M : Cat A X),
    FiniteFreeCoefficients.Ctf A X K → FiniteFreeCoefficients.Ctf A X M →
      (Etale.scalarExtension φ Y).map (pullHom A e.hom K M) ≫
        FiniteFreeCoefficients.homMap φ Y ((pull A e.hom).obj K) ((pull A e.hom).obj M) ≫
        homAction (Etale.derivedHom (ModuleCat.{u + 1} B) Y)
          ((scalarPull φ e.hom).hom.app K)
          ((scalarPull φ e.hom).inv.app M) =
      (scalarPull φ e.hom).inv.app
          (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ≫
        (pull B e.hom).map (FiniteFreeCoefficients.homMap φ X K M) ≫
        pullHom B e.hom ((Etale.scalarExtension φ X).obj K) ((Etale.scalarExtension φ X).obj M)


/-- The exceptional coefficient mate commutes with isomorphism base change.
At a closed immersion this is the unique closed counit mate; at the structure morphism
and the unit it is precisely dualizing naturality. Verdier naturality is their composite
with HomGeometry. The base is allowed to move, as required for geometric Frobenius.
Source: blueprint main-20261015, lem-coef-finite-free-extension, scheme-isomorphism
naturality, including geometric Frobenius (blueprint: lem-coef-finite-free-extension). -/
def ExceptionalGeometry {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S}
    [QuasiCompact f] (c : Compactification f) (M : Cat A S) : Prop :=
  letI := c.hasCompactification
  ∀ (S' : Scheme.{u}) (e : S' ≅ S),
    Etale.ExceptionalCoefficients.BaseChangeCompatibility φ f e.hom M


/-- Inverse on the isomorphism domain, extended by zero elsewhere.
Source: blueprint finite constructible comparison domains
(blueprint: lem-coef-finite-free-extension). -/
def inverseOnDomain {C : Type w} [Category.{v} C] [Preadditive C]
    {K M : C} (b : K ⟶ M) : M ⟶ K :=
  open Classical in
  if h : IsIso b then @inv _ _ _ _ b h else 0

/-- Actual pro-etale inverse image used by scheme-isomorphism naturality.
Source: blueprint geometric coefficient squares
(blueprint: lem-coef-finite-free-extension). -/
def proPull (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X) :=
  L(ProEtale.upperStar (ModuleCat.{u + 1} A) g)

/-- Canonical derived scalar/pullback comparison from the restriction/direct-image identity.
Source: blueprint geometric coefficient squares and the fixed scalar adjunctions
(blueprint: lem-coef-finite-free-extension). -/
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
(blueprint: lem-coef-finite-free-extension). -/
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
(blueprint: lem-coef-finite-free-extension). -/
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
(blueprint: lem-coef-finite-free-extension). -/
def rnuPull (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X)
    (M : D true A X) :
    (pull A g).obj ((rnu A X).obj M) ⟶ (rnu A Y).obj ((proPull A g).obj M) :=
  (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ _
    ((sitePull A g).inv.app ((rnu A X).obj M) ≫
      (proPull A g).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app M))

/-- Canonical closed coefficient map on the pro-etale transported exceptional functor.
Source: blueprint transported closed-exceptional comparison, with the site counit mate
(blueprint: lem-coef-finite-free-extension). -/
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
(blueprint: lem-coef-finite-free-extension). -/
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

/-- Closed base change on the transported pro-etale exceptional functor.
Source: blueprint site transport of the closed counit square
(blueprint: lem-coef-finite-free-extension). -/
def proClosedPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (g : Y ⟶ X)
    (M : D true A X) :
    (proPull A (pullback.fst i g)).obj ((exceptional true A i).obj M) ⟶
      (exceptional true A (pullback.snd i g)).obj ((proPull A g).obj M) :=
  (sitePull A (pullback.fst i g)).hom.app ((closedUpper A i).obj ((rnu A X).obj M)) ≫
    (nu A (pullback i g)).map (closedPull A i g ((rnu A X).obj M)) ≫
    (nu A (pullback i g)).map ((closedUpper A (pullback.snd i g)).map (rnuPull A g M))

/-- The closed coefficient map, including its actual ordinary adjoint, is geometric.
Source: blueprint closed-exceptional scheme-isomorphism square
(blueprint: lem-coef-finite-free-extension). -/
def ClosedGeometry {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  ∀ (Y : Scheme.{u}) (e : Y ≅ X) (M : Cat A X), FiniteFreeCoefficients.Ctf A X M →
    (scalar false φ (pullback i e.hom)).map (closedPull A i e.hom M) ≫
      FiniteFreeCoefficients.closedMap φ (pullback.snd i e.hom) ((pull A e.hom).obj M) ≫
      (closedUpper B (pullback.snd i e.hom)).map ((scalarPull φ e.hom).inv.app M) =
    (scalarPull φ (pullback.fst i e.hom)).inv.app ((closedUpper A i).obj M) ≫
      (pull B (pullback.fst i e.hom)).map (FiniteFreeCoefficients.closedMap φ i M) ≫
      closedPull B i e.hom ((scalar false φ X).obj M)

/-- The same closed geometric square on the recorded pro-etale finite-Tor domain.
Source: blueprint closed-exceptional scheme-isomorphism square on the pro-etale realization
(blueprint: lem-coef-finite-free-extension). -/
def ProClosedGeometry {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  ∀ (Y : Scheme.{u}) (e : Y ≅ X) (M : D true A X), Ctf true A X M →
    (scalar true φ (pullback i e.hom)).map (proClosedPull A i e.hom M) ≫
      proClosedMap φ (pullback.snd i e.hom) ((proPull A e.hom).obj M) ≫
      (exceptional true B (pullback.snd i e.hom)).map ((proScalarPull φ e.hom).inv.app M) =
    (proScalarPull φ (pullback.fst i e.hom)).inv.app ((exceptional true A i).obj M) ≫
      (proPull B (pullback.fst i e.hom)).map (proClosedMap φ i M) ≫
      proClosedPull B i e.hom ((scalar true φ X).obj M)

/-- The direct-image square under the canonical pullback by a scheme isomorphism.
Source: blueprint main-20261015, lem-coef-finite-free-extension, scheme-isomorphism
naturality, including geometric Frobenius (blueprint: lem-coef-finite-free-extension). -/
def ProDirectGeometry {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X) : Prop :=
  ∀ (Y : Scheme.{u}) (e : Y ≅ X) (K : D true A T), Ctf true A T K →
    (scalar true φ Y).map
        ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback f e.hom).toCommSq).app K) ≫
      ProEtale.finiteCoefficientChangeDirectImageMap φ (pullback.snd f e.hom)
        ((proPull A (pullback.fst f e.hom)).obj K) ≫
      (R(ProEtale.lowerStar (ModuleCat.{u + 1} B) (pullback.snd f e.hom))).map
        ((proScalarPull φ (pullback.fst f e.hom)).inv.app K) =
    (proScalarPull φ e.hom).inv.app
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
      (proPull B e.hom).map (ProEtale.finiteCoefficientChangeDirectImageMap φ f K) ≫
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} B)
        (IsPullback.of_hasPullback f e.hom).toCommSq).app ((scalar true φ T).obj K)



/-- Pullback of pro-etale internal Hom is the transpose of pulled-back evaluation.
Source: blueprint geometric Hom and evaluation square
(blueprint: lem-coef-finite-free-extension). -/
def proPullHom (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (g : Y ⟶ X)
    (K M : D true A X) :
    (proPull A g).obj (((hom true A X).obj (op K)).obj M) ⟶
      ((hom true A Y).obj (op ((proPull A g).obj K))).obj ((proPull A g).obj M) :=
  (adj true A Y ((proPull A g).obj K)).homEquiv _ _
    ((ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K
      (((hom true A X).obj (op K)).obj M)).inv ≫
        (proPull A g).map ((adj true A X K).counit.app M))

/-- Pro-etale geometric Hom square for the representative-normalized tensor comparisons.
Source: blueprint geometric internal-Hom naturality
(blueprint: lem-coef-finite-free-extension). -/
def ProHomGeometry {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : TensorComparison true φ X) : Prop :=
  ∀ (Y : Scheme.{u}) (e : Y ≅ X) (δ : TensorComparison true φ Y),
    NormalizedTensor true φ Y δ → ∀ K M : D true A X, Ctf true A X K → Ctf true A X M →
      (scalar true φ Y).map (proPullHom A e.hom K M) ≫
        homMap true φ Y δ ((proPull A e.hom).obj K) ((proPull A e.hom).obj M) ≫
        homAction (hom true B Y) ((proScalarPull φ e.hom).hom.app K)
          ((proScalarPull φ e.hom).inv.app M) =
      (proScalarPull φ e.hom).inv.app (((hom true A X).obj (op K)).obj M) ≫
        (proPull B e.hom).map (homMap true φ X μ K M) ≫
        proPullHom B e.hom ((scalar true φ X).obj K) ((scalar true φ X).obj M)

/-- The pro-etale dualizing coefficient map in canonical site coordinates.
Source: blueprint dualizing site square
(blueprint: lem-coef-finite-free-extension). -/
def proOmegaMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    (scalar true φ X).obj (omega true A c) ⟶ omega true B c :=
  (scalar true φ X).map (inverseOnDomain (omegaBridge A c)) ≫
    (scalarSite φ X).hom.app (FiniteFreeCoefficients.omega A c) ≫
    (nu B X).map (FiniteFreeCoefficients.omegaMap φ c) ≫ omegaBridge B c

/-- Dualizing isomorphism base change, with its regular-unit identification.
Source: blueprint dualizing geometric square
(blueprint: lem-coef-finite-free-extension). -/
def proOmegaPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    (c : Compactification f) (g : S' ⟶ S) :
    (proPull A (pullback.fst f g)).obj (omega true A c) ⟶
      omega true A (c.baseChange g) := by
  letI := c.hasCompactification
  exact (proPull A (pullback.fst f g)).map (inverseOnDomain (omegaBridge A c)) ≫
    (sitePull A (pullback.fst f g)).hom.app (FiniteFreeCoefficients.omega A c) ≫
    (nu A (pullback f g)).map (Etale.smoothDualizingBaseChangeMap A f g) ≫
    omegaBridge A (c.baseChange g)

/-- Pro-etale dualizing geometry on the actual base-changed compactification.
Together with ProHomGeometry this also gives the geometric Verdier square.
Source: blueprint dualizing and Verdier geometric naturality
(blueprint: lem-coef-finite-free-extension). -/
def ProOmegaGeometry {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    (c : Compactification f) : Prop :=
  ∀ (S' : Scheme.{u}) (e : S' ≅ S),
    (scalar true φ (pullback f e.hom)).map (proOmegaPull A c e.hom) ≫
      proOmegaMap φ (c.baseChange e.hom) =
    (proScalarPull φ (pullback.fst f e.hom)).inv.app (omega true A c) ≫
      (proPull B (pullback.fst f e.hom)).map (proOmegaMap φ c) ≫
      proOmegaPull B c e.hom

end Sites


/-- Finite free coefficient extensions on the cofinal ramified levels, including all five
canonical comparisons on both small sites, all coefficient cocycles and the scheme-isomorphism
squares. The index `Stage` uses the base uniformizer, so ramification is retained.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-free-extension (blueprint: lem-coef-finite-free-extension).

Proof, following the node's complete proof:

1. The restriction of $|\cdot|_L$ to $E$ equals $|\cdot|_E$ by uniqueness [lem-weil-l-adic-
extension-absolute-value]; hence $\mathcal O_E=E\cap\mathcal O_L$ and $0<|\varpi_E|_L<1$. Apply
the uniformizer factorization in [lem-weil-l-adic-extension-integers-dvr] in $L$:
$\varpi_E=u\varpi_L^e$ for a unit $u$ and a positive integer $e$, the ramification index.
Consequently $\varpi_E^n\mathcal O_L=\varpi_L^{en}\mathcal O_L$ for all $n$. The quotient
$\mathcal O_L/\varpi_E\mathcal O_L$ is finite by [lem-weil-valued-dvr-finite-quotients] at
exponent $e$ in $L$. It is therefore a finitely generated module over $\mathcal O_E/\varpi_E$: the
images of all its finitely many elements are a generating set.

2. The ring $R=\mathcal O_E$ is $(\varpi_E)$-adically complete. Indeed, for a compatible sequence
of residues choose lifts $x_n\in R$; then $x_{n+1}-x_n\in\varpi_E^nR$, so $(x_n)$ is Cauchy and
converges by [lem-weil-l-adic-extension-complete]. Its limit is in $R$ and has the prescribed
residues because $\varpi_E^nR=\{x:|x|_E\le |\varpi_E|_E^n\}$ is closed. The intersection of these
balls is zero, so the lift is unique, proving the definition [def-weil-pbc-adically-complete-
ring]. If $y\in\bigcap_n\varpi_E^n\mathcal O_L$, then $|y|_L\le |\varpi_E|_L^n$ for every $n$.
Since $0<|\varpi_E|_L<1$, this forces $|y|_L=0$, hence $y=0$. Apply [lem-weil-pbc-finite-over-
complete-ring] to $R$, $I=(\varpi_E)$ and $M=\mathcal O_L$ using the finite residue module of step
1. Thus $\mathcal O_L$ is finite over $R$. It is torsion-free since it is a subring of the field
$L$ and $R\hookrightarrow L$ is injective; $R$ is a DVR by [lem-weil-l-adic-extension-integers-
dvr]. Hence [lem-sc-dvr-fg-torsionfree-free] gives an $R$-basis $b_1,\ldots,b_r$ of $\mathcal
O_L$. Reducing this basis gives $B\cong A^{\oplus r}$ as $A$-modules.

3. On either coefficient site write $T_W=-\otimes_A B_W$ and $U_W$ for restriction of scalars
[def-pc-sheaf-restrict-scalars]. Apply [lem-weil-pbc-ringed-topoi-module-adjunction] to the
identity topos and $A_W\to B_W$: $T_W\dashv U_W$. By [lem-pur-change-of-rings-tensor-comparison]
and the basis in step 2, $U_WT_WN\cong N^{\oplus r}$. Thus $T_W$ is exact; $U_W$ is exact and
reflects zero objects because it leaves the underlying abelian sheaf unchanged. The exact functors
descend termwise by [lem-weil-pbc-exact-functor-derived-factorization]. The termwise unit and
counit of [lem-weil-pbc-termwise-adjunction-homotopy] descend as well and retain their triangle
identities, so $T_W\dashv U_W$ also on derived categories, and $U_W$ reflects isomorphisms (apply
it to the cohomology of a cone). The exact derived $T_W$ is the derived change of rings of [lem-
pur-derived-change-of-rings]. Tensor extension preserves bounded constructibility: it is exact,
and on each stratum a finite locally constant $A$-module becomes a finite locally constant
$B$-module. It preserves any Tor interval $[a,b]$ because $(T_WK)\otimes_B^L N\cong K\otimes_A^L
U_WN$, on K-flat tensor complexes [lem-weil-pbc-site-derived-tensor-descent]: the balanced maps
are $(p\otimes b)\otimes n\mapsto p\otimes bn$ and $p\otimes n\mapsto(p\otimes1)\otimes n$. They
are inverse chain maps; extension of a K-flat $A$-complex is K-flat over $B$, since this formula
identifies its tensor with an acyclic $B$-complex with tensor against that complex restricted to
$A$, which is acyclic because $U$ is exact.

4. First work etale. For a $B$-complex $N$ the canonical comparison $U_XRf_{*,B}N\cong
Rf_{*,A}U_TN$ is [lem-sbc-canonical-restrict-scalars-functor-comparisons] on bounded-below
objects. For a finite-free extension the same comparison is available on unbounded objects
directly: a $B$-K-injective resolution remains $A$-K-injective by [lem-weil-pbc-right-adjoint-
preserves-kinjective], since $T_T$ is exact, and direct image commutes sectionwise with $U$. Under
this identification the underlying map of the projection comparison $c_f:T_XRf_{*,A}K\to
Rf_{*,B}T_TK$ [def-kun-projection-formula-map] is the finite-sum comparison $(Rf_{*,A}K)^{\oplus
r}\to Rf_{*,A}(K^{\oplus r})$. To verify the map, precompose with its $j$-th summand: the
projection map is adjoint to the inverse-image counit, and the component is $Rf_*$ applied to the
inclusion $k\mapsto k\otimes b_j$; these are exactly the finite-sum inclusions. Any additive
functor $F$ preserves this finite sum explicitly: applying $F$ to projections $p_j$ and inclusions
$s_j$ preserves $p_js_h=\delta_{jh}$ and $\sum_js_jp_j=1$, giving inverse comparison matrices.
Apply this to $Rf_{*,A}$. Thus $U_Xc_f$, and hence $c_f$, is invertible. This proves the first
displayed comparison without any cohomological-dimension hypothesis.

5. For compact supports, factor the chosen morphism as an open immersion followed by a proper
morphism. A separated finite-type morphism between our schemes is compactifiable by [thm-nagata-
compactification], and the schemes in the compactification are Noetherian by [lem-weil-pbc-finite-
type-over-noetherian]: a field has only the zero and unit ideals, so $\operatorname{Spec}k$ is
Noetherian, and each scheme here is finite type over it. For a fixed $f:T\xrightarrow{j}\overline
T\xrightarrow{p}X$ with $\overline T$ finite type over $X$, the etale functor is $F_A=Rp_{*,A}j_!$
[def-amb-etale-compact-support]. Extension by zero commutes with coefficient extension and
restriction: off the open its stalk is zero, and on the open it is the given stalk [lem-weil-pbc-
extension-by-zero-stalks, lemma-weil-pbc-geometric-stalk-conservative]; the comparison is the map
induced by $m\otimes b\mapsto m\otimes b$. Combining this with step 4 for $p$ gives
$c^!_f:T_XF_A\xrightarrow{\sim}F_BT_T$, natural in all objects. After restriction it is the
finite-sum comparison, whose components are $F_A$ of the inclusions $m\mapsto m\otimes b_j$. This
construction also applies to the structure morphism $a_X$.

6. Apply extension and restriction of scalars to the two exceptional adjunctions. Let $F_A\dashv
G_A$ and $F_B\dashv G_B$ be either $i_*\dashv Ri^!$ [lem-exc-closed-ambient], or $Ra_{X!}\dashv
a_X^{\times}$ [thm-amb-etale-exceptional-adjoint]. Their left functors have the comparison $c:T
F_A\xrightarrow{\sim}F_BT$ of steps 4 and 5 (for $i_*$ use its derived direct image). For a
$B$-object $N$ and an $A$-test object $P$, the successive adjunctions give $$\operatorname{Hom}_A(
P,UG_BN)=\operatorname{Hom}_B(TP,G_BN)=\operatorname{Hom}_B(F_BTP,N)=\operatorname{Hom}_B(TF_AP,N)
=\operatorname{Hom}_A(F_AP,UN)=\operatorname{Hom}_A(P,G_AUN).$$ The bijections are natural in
$P,N$; they therefore identify $UG_BN$ with $G_AUN$: evaluate the bijection and its inverse at
identity maps to obtain inverse morphisms. Define $b_M:TG_AM\to G_BTM$ to be adjoint to
$(T\varepsilon_{A,M})c_{G_AM}^{-1}$. Under the preceding identification and $UTM=M^{\oplus r}$,
$Ub_M$ is the map $(G_AM)^{\oplus r}\to G_A(M^{\oplus r})$ whose $j$-th component is $G_A$ of the
$j$-th inclusion; this follows by transposing that component, which gives precisely
$\varepsilon_{A,M}$ followed by that inclusion. The finite-sum matrix calculation of step 4 makes
this an isomorphism. Since $U$ reflects isomorphisms, $b_M$ is an isomorphism. The two choices of
$F,G$ give the closed-exceptional comparison and, at $M=A_s$, the dualizing comparison
$u:T\omega_{X,A}\xrightarrow{\sim}\omega_{X,B}$. By definition they obey
$\varepsilon_{B,TM}F_B(b_M)=(T\varepsilon_{A,M})c_{G_AM}^{-1}$, which is the required counit
identity.

7. The derived tensor--Hom adjunction is the composite $$\operatorname{Hom}(L,H_A(K,N))\cong
H^0(\mathcal C,H_A(L,H_A(K,N)))\cong H^0(\mathcal
C,H_A(L\otimes_A^LK,N))\cong\operatorname{Hom}(L\otimes_A^LK,N),$$ using [lem-pur-rhom-global-
sections] and [lem-weil-pbc-ringed-internal-hom-exact-restriction]. Its counit is evaluation, so
the comparison $v_{K,M}$ is the transpose of scalar-extended evaluation pairing.

8. For the finite-free constant ring extension of step 2, [lem-sf-ringed-finite-free-hom-base-
change] gives an isomorphism $$T H_A(K,M)\xrightarrow{\sim}H_B(TK,TM)$$ whose defining transpose
is exactly the evaluation pairing from the preceding step. Therefore this isomorphism is the map
$v_{K,M}$, and it requires no perfectness hypothesis on $K$.

9. Define $\beta_K$ as $v_{K,\omega_{X,A}}$ followed by $R\mathcal Hom_B(TK,u)$. Steps 6 and 8
make it an isomorphism $TD_{X,A}K\to D_{X,B}TK$. Its evaluation identity is
$$u\,T(\mathrm{ev}_{A,K})=\mathrm{ev}_{B,TK}(\beta_K\otimes1),$$ where tensor reassociation is
understood. Indeed, both sides send a functional tensored with $k$ and coefficient $b$ to its
value multiplied by $b$, followed by $u$; this is exactly the defining transposition in step 7.
The double-dual map is the transpose of evaluation [lem-weil-duality-pairing], so transposing this
identity once more gives $$\beta_{D_AK}\,T(\delta_{A,K})=D_B(\beta_K)\,\delta_{B,TK}.$$ This is
the double-dual compatibility (both sides land in $D_B(TD_AK)$). In particular, it does not
presume biduality in order to prove compatibility.

10. The basis was used only to test invertibility. All five maps were defined before choosing a
basis by projection, counit or evaluation. For $E\subset L\subset H$, put $d=e(H/L)$ and
$C=\mathcal O_H/\varpi_E^n\mathcal O_H=A_{H,den}$. The factorization $\varpi_E=u\varpi_L^e$ and
$\varpi_L=v\varpi_H^d$ gives $\varpi_E=uv^e\varpi_H^{de}$ with a unit coefficient, so the iterated
coefficient stage is exactly $C$. Compare the maps for $A\to B\to C$ with that for $A\to C$, using
$(K\otimes_A B)\otimes_B C\cong K\otimes_A C$. This reassociation and its action on morphisms can
be checked on K-flat tensor complexes [lem-weil-pbc-site-derived-tensor-descent]. For direct
image, under the inverse-image adjunction both composite maps have transpose $f^*Rf_*K\otimes_A
C\to K\otimes_A C$, the inverse-image counit tensored with $C$. For exceptional and dualizing
maps, their transposes are respectively $F_C(T_{A,C}G_AM)\xrightarrow{(c_{A,C})^{-
1}}T_{A,C}F_AG_AM\xrightarrow{T_{A,C}\varepsilon_A}T_{A,C}M$; expanding either composite gives
this formula, since the intermediate $F_B\dashv G_B$ unit followed by counit cancels by its
triangle identity. For internal Hom the transpose of either composite is $T_{A,C}(\mathrm{ev}_A)$
after tensor reassociation. Adjunction is a bijection on morphisms, so equality of these displayed
transposes proves each composition law, and composition proves the Verdier law. For the identity
extension the same transposes are the original counit/evaluation, giving the identity comparisons.

11. Write $A_n=A_{E,n}$, $B_n=A_{L,en}$ and similarly $A_m,B_m$, with $1\le m\le n$. Since $B_n$
is free over $A_n$ by step 2, $$B_n\otimes^L_{A_n}A_m=B_n/\varpi_E^mB_n=B_m.$$ The K-flat
reassociation of [lem-weil-pbc-site-derived-tensor-descent] identifies both iterated scalar
extensions in the reduction square with tensoring directly to $B_m$; the balanced map is
$(p\otimes a)\otimes b\mapsto p\otimes ab$.

12. Apply [lem-coef-finite-direct-image], [lem-coef-finite-closed-shriek], [lem-coef-finite-
dualizing], [thm-coef-finite-hom] and [cor-coef-finite-verdier] to the same-field quotient maps
$(A_n\to A_m)$ and $(B_n\to B_m)$. Step 3 supplies finite-Tor constructibility after extension to
$B_n$, and $en\ge em\ge1$, so all five comparisons have the required inputs and outputs. The
closed-exceptional comparison is first obtained on the pro-etale realization.

13. The coefficient-reduction squares for direct image, closed exceptional image, and the
dualizing object commute by the mate-pasting identities [lem-weil-pbc-mate-pasting]. Their mates
are respectively the direct-image counit, the exceptional counit, and the compact-support counit
tensored to $B_m$; intermediate unit/counit pairs cancel by the triangle identities. The finite-
Tor hypotheses for dualizing inputs are supplied by [lem-weil-verdier-preservation-strata].

14. The constant rank-one complexes $A_X$ and $B_X$ are finite-Tor constructible, and their duals
are $\omega_{X,A}$ and $\omega_{X,B}$. Hence [lem-weil-verdier-preservation-strata] gives finite-
Tor constructibility for these dualizing objects and every dual input in the quotient comparisons.

15. For internal Hom use [lem-weil-pbc-mate-pasting] on the tensor–Hom adjunction from step 7.
Tensor reassociation identifies the pasted left squares; both right mates have transpose
evaluation tensored to $B_m$. [thm-coef-finite-hom] identifies the quotient maps with precisely
these evaluation transposes at $(n,m)$ over $E$ and $(en,em)$ over $L$. Thus the internal-Hom
reduction square commutes. Composing it with the dualizing square gives the Verdier square [cor-
coef-finite-verdier]. The evaluation identity and its double-dual transpose from step 9 persist
after derived tensor; [lem-weil-verdier-preservation-strata] verifies finite-Tor constructibility
for the dual inputs in these quotient comparisons.

16. These comparisons give the finite-coefficient pro-étale assertions. Direct image commutes with
comparison pullback by [lem-weil-pbc-comparison-direct-image-canonical-mate]: $f$ is qcqs and its
input bounded below. Tensor pullback commutes with derived tensor by [lem-weil-pbc-ringed-topoi-
derived-tensor-pullback]. The exceptional functor is the transported étale functor [def-weil-
exceptional-inverse-image]. The dualizing and internal-Hom identifications, including evaluation
and double-dual, are [lem-weil-finite-duality-site-comparison] at each finite coefficient stage:
its first input is finite-Tor, its second bounded constructible, including the dualizing objects
established above. To identify the maps, paste the site-comparison and coefficient squares using
[lem-weil-pbc-mate-pasting]. The canonical-mate counit normalization identifies the pulled-back
inverse-image counit with the pro-étale counit. After tensor comparison the pulled-back projection
transpose is therefore that counit tensored with $B$. For internal Hom the transpose is pulled-
back evaluation; for the exceptional map it is the transported étale exceptional counit.
Consequently these are the named coefficient maps on the pro-étale realization, and the functor
carries all previously proved map identities to it.

17. The remaining recovery of the étale closed-exceptional quotient map is [lem-coef-finite-etale-
descent], applied over $E$ at $(n,m)$ and over $L$ at $(en,em)$. Its input is finite-Tor
constructible on the étale site by the hypotheses and step 3. It places both étale outputs in the
same finite-Tor constructible category and identifies its pulled-back counit-defined map with
[lem-coef-finite-closed-shriek]. Its faithfulness clause then descends the pro-étale mixed
reduction square just proved. Thus this use of the pro-étale closed coefficient theorem recovers
exactly the étale map and square, with their required output typing.

18. Finally, transport a diagram along scheme isomorphisms (and the base isomorphism when
present). The induced site equivalences identify module sheaves by inverse reindexing; their
inverse transports are actual inverses up to the canonical pullback identifications. The formula
for tensor, scalar extension, the Hom differential, and evaluation is unchanged under this
reindexing. Transport the left adjunction and its unit/counit as well. The transported right
adjoint is the original right adjoint under the unique counit-compatible identification; after
bringing both functors into the same categories this uniqueness is [lem-trf-adjoint-mate].
Consequently the transported comparison is the comparison on the transported diagram: both have
exactly the projection-counit or evaluation transposes displayed in steps 4, 6, 7 and 9. This
includes the semilinear Frobenius isomorphism of [def-weil-global-geometric-frobenius] because
$\gamma$ is a field automorphism with inverse. Lastly $e\ge1$ and for every $m\ge1$ there is
$n\ge1$ with $en\ge m$ (take $n=m$); the set of such $n$ is a nonempty tail and hence directed.
Thus the indices $en$ are cofinal for the inverse tower. The ideal equality in step 1 identifies
exactly those levels with $B_n$; changing either uniformizer by a unit does not change these
ideals or quotient maps.
-/
theorem finite_free_coefficient_extension (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∀ s : Stage l E, ∃ (e : ℕ+) (z : s.integersˣ),
      s.parameter = (z : s.integers) * Padic.coefficientExtensionUniformizer l s.field ^ (e : ℕ) ∧
      (∀ n : ℕ, Ideal.span ({s.parameter} : Set s.integers) ^ n =
        Padic.coefficientExtensionIdeal l s.field ((e : ℕ) * n)) ∧
      ∀ r : ℕ, ∃ n : ℕ+, r ≤ (e : ℕ) * (n : ℕ)) ∧
    (∀ (s t : Stage l E) (a : Arrow s t), s.exponent = t.exponent → a.IsFiniteFree) ∧
    (∀ (T X Z : Scheme.{u})
      [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
      [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
      [QuasiCompact (T ↘ Spec (.of D.k))]
      [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
      [QuasiCompact (X ↘ Spec (.of D.k))]
      [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
      [QuasiCompact (Z ↘ Spec (.of D.k))]
      (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
      (c : Compactification (X ↘ Spec (.of D.k))),
      ∃ (et : Sites.Calculus false l E f i c) (pro : Sites.Calculus true l E f i c),
        Sites.Normalized l E f i c et pro ∧
        ∀ {s t : Stage l E} (a : Arrow s t),
          Sites.DirectGeometry a.ringMap f ∧ Sites.HomGeometry a.ringMap X ∧
          Sites.ClosedGeometry a.ringMap i ∧
          Sites.ExceptionalGeometry a.ringMap c (𝟙_ _) ∧
          Sites.ProDirectGeometry a.ringMap f ∧
          Sites.ProClosedGeometry a.ringMap i ∧
          Sites.ProHomGeometry a.ringMap X (pro.tensorIso a) ∧
          Sites.ProOmegaGeometry a.ringMap c ∧
          (∀ M : Sites.D true s.ring X, Sites.Ctf true s.ring X M →
            pro.closedMap a M = Sites.proClosedMap a.ringMap i M) ∧
          pro.omegaMap a = Sites.proOmegaMap a.ringMap c) := by
  sorry

end WeilConjectures.FiniteFreeCoefficients
