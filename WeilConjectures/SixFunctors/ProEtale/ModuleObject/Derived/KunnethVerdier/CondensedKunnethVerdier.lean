/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps2
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
public import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
public import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BidualityCoefficients
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # External duality and the correspondence trace

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/_section.md,
correspondence assertions and General form (blueprint: sk-thm-sf-kunneth-verdier).

All exceptional functors below are the recorded constructible adjoints. No ambient
exceptional adjoint or exceptional-admissibility assumption is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.KunnethVerdier

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (hne : ringChar D₀.k ≠ ell)
  (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)

/-- The characteristic-prime instance follows from the fixed finite-field datum.
Source: standing field convention (blueprint: sk-thm-sf-kunneth-verdier).
Proof. The cardinality of the base field gives CharP D₀.k₀ D₀.p, and the
injective algebra map transports it to D₀.k. Hence ringChar.eq
identifies ringChar D₀.k with D₀.p; transport the stored proof D₀.prime. -/
theorem characteristicPrime : Fact (ringChar D₀.k).Prime := by
  let : Fintype D₀.k₀ := Fintype.ofFinite D₀.k₀
  let : Fact D₀.p.Prime := ⟨D₀.prime⟩
  let : CharP D₀.k₀ D₀.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D₀.card_base.trans D₀.cardinality_eq)
  let : CharP D₀.k D₀.p := charP_of_injective_algebraMap' D₀.k₀ D₀.p
  exact ⟨(ringChar.eq D₀.k D₀.p).symm ▸ D₀.prime⟩

/-- The specified Brown adjunction for the chosen Nagata compactification.
Source: det-def-sf-operations (vi) (blueprint: sk-thm-sf-kunneth-verdier). -/
def chosenAdjunction {X Y : SepFinType D₀.k} (f : X ⟶ Y) :=
  letI := characteristicPrime D₀
  letI : Fact (ringChar D₀.k ≠ ell) := ⟨hne⟩
  sixOperationsLocalizingAdjunction Λ.X ell D₀.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D₀.k) f.hom hΛ

/-- The actual constructible exceptional inverse image on the chosen model.
Source: det-def-sf-operations (vi) (blueprint: sk-thm-sf-kunneth-verdier). -/
def exceptional {X Y : SepFinType D₀.k} (f : X ⟶ Y) :=
  ProductComparisons.exceptional Λ (chosenAdjunction D₀ ell hne Λ hΛ f)

/-- The actual constructible compact-support functor on the same model.
Source: det-def-sf-operations (vi) (blueprint: sk-thm-sf-kunneth-verdier). -/
def support {X Y : SepFinType D₀.k} (f : X ⟶ Y) :=
  ProductComparisons.lower Λ (chosenAdjunction D₀ ell hne Λ hΛ f)

/-- Their original restricted Hom bijections.
Source: det-def-sf-operations (vi) (blueprint: sk-thm-sf-kunneth-verdier). -/
def adjunction {X Y : SepFinType D₀.k} (f : X ⟶ Y) :
    support D₀ ell hne Λ hΛ f ⊣ exceptional D₀ ell hne Λ hΛ f :=
  ProductComparisons.adjunction Λ (chosenAdjunction D₀ ell hne Λ hΛ f)

/-- The current recorded Brown restriction in the same finite-field geometric setting.
Source: det-def-sf-operations (vi), currentConstructibleExceptionalData
(blueprint: sk-thm-sf-kunneth-verdier). -/
def currentAdjunction {X Y : SepFinType D₀.k} (f : X ⟶ Y) :=
  letI := characteristicPrime D₀
  letI : Fact (ringChar D₀.k ≠ ell) := ⟨hne⟩
  currentConstructibleExceptionalData Λ.X ell D₀.k (Or.inr inferInstance) f.hom hΛ

/-- The support model agrees with the current recorded restriction, through its
specified equality on the ambient functor. The full inclusion reflects this iso.
Source: det-def-sf-operations (vi), lower_eq
(blueprint: sk-thm-sf-kunneth-verdier). -/
def currentSupportComparison {X Y : SepFinType D₀.k} (f : X ⟶ Y) :
    (currentAdjunction D₀ ell hne Λ hΛ f).lower ≅ support D₀ ell hne Λ hΛ f :=
  Functor.fullyFaithfulCancelRight
    (constantModelBoundedConstructible Λ.X Y.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι
    (eqToIso (currentAdjunction D₀ ell hne Λ hΛ f).lower_eq)

/-- The exceptional model is identified with the current recorded right adjoint by
the mate of lower_eq. Thus its exceptional counit is transported together with the
functor, rather than choosing an unrelated comparison.
Source: det-def-sf-operations (vi), adjunction
(blueprint: sk-thm-sf-kunneth-verdier). -/
def currentExceptionalComparison {X Y : SepFinType D₀.k} (f : X ⟶ Y) :
    exceptional D₀ ell hne Λ hΛ f ≅ (currentAdjunction D₀ ell hne Λ hΛ f).right :=
  conjugateIsoEquiv (adjunction D₀ ell hne Λ hΛ f)
    (currentAdjunction D₀ ell hne Λ hΛ f).adjunction
    (currentSupportComparison D₀ ell hne Λ hΛ f)

set_option linter.defProp false in
/-- Ordinary pullback restricted by the published preservation theorem.
Source: ordinary adjunction in the proof (blueprint: sk-thm-sf-kunneth-verdier). -/
def pull {X Y : SepFinType D₀.k} (f : X ⟶ Y) :=
  (constantModelBoundedConstructible Λ.X X.obj.left ⊓
    _root_.DerivedCategory.finiteTorAmplitude _).lift
    ((constantModelBoundedConstructible Λ.X Y.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙ P Λ.X f.hom.left)
    (fun K ↦ (stability D₀ ell hne Λ hΛ f).1 K)

/-- Ordinary direct image restricted by the same preservation theorem.
Source: ordinary adjunction in the proof (blueprint: sk-thm-sf-kunneth-verdier). -/
def direct {X Y : SepFinType D₀.k} (f : X ⟶ Y) :=
  (constantModelBoundedConstructible Λ.X Y.obj.left ⊓
    _root_.DerivedCategory.finiteTorAmplitude _).lift
    ((constantModelBoundedConstructible Λ.X X.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙ R Λ.X f.hom.left)
    (fun K ↦ (stability D₀ ell hne Λ hΛ f).2.1 K)

/-- The ordinary restricted adjunction retains its original unit and counit.
Source: proof, trace construction (blueprint: sk-thm-sf-kunneth-verdier). -/
def ordinaryAdjunction {X Y : SepFinType D₀.k} (f : X ⟶ Y) :
    pull D₀ ell hne Λ hΛ f ⊣ direct D₀ ell hne Λ hΛ f :=
  (derivedUpperStarLowerStarAdjunction Λ.X f.hom.left).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)

/-- The coefficient unit at the point, with its actual constructibility proof.
Source: sk-def-ops (blueprint: sk-thm-sf-kunneth-verdier). -/
def unit : ConstantModelConstructibleFiniteTor Λ.X (Spec (.of D₀.k)) :=
  ⟨𝟙_ _, condensedCoefficientUnit_mem Λ.X (Spec (.of D₀.k))⟩

/-- The structure map of a separated finite-type scheme.
Source: sk-def-ops (blueprint: sk-thm-sf-kunneth-verdier). -/
def structureMap (X : SepFinType D₀.k) : X ⟶ ProductComparisons.base D₀.k :=
  ObjectProperty.homMk (Over.mkIdTerminal.from X.obj)

/-- Relative internal Hom as a constructible object, using the recorded preservation.
Source: sk-def-ops and stability (blueprint: sk-thm-sf-kunneth-verdier). -/
def homObject (X : SepFinType D₀.k)
    (K L : ConstantModelConstructibleFiniteTor Λ.X X.obj.left) :
    ConstantModelConstructibleFiniteTor Λ.X X.obj.left :=
  ⟨(ihom K.obj).obj L.obj, (stability D₀ ell hne Λ hΛ (𝟙 X)).2.2.2.2.1 K L |>.2⟩

/-- Chosen compactifications of all morphisms in a product diagram. They are models,
not admissibility inputs. Source: sk-def-sf-kv-maps (i)
(blueprint: sk-thm-sf-kunneth-verdier). -/
def models (G : ProductComparisons.Geometry D₀.k) : ProductComparisons.Models G where
  f₁ := compactificationOverField G.f₁.hom
  f₂ := compactificationOverField G.f₂.hom
  relative :=
    { f := compactificationOverField G.u.hom
      g := compactificationOverField G.v.hom
      q := compactificationOverField G.q.hom
      total := compactificationOverField (G.q ≫ G.v).hom }

set_option maxHeartbeats 1600000 in
-- The normalized derived-functor transports elaborate several large closed-category instances.
/-- Tensor of constructible finite-Tor objects, with its published preservation proof.
Source: stability used in the correspondence proof
(blueprint: sk-thm-sf-kunneth-verdier). -/
def tensorObject (X : SepFinType D₀.k)
    (K L : ConstantModelConstructibleFiniteTor Λ.X X.obj.left) :
    ConstantModelConstructibleFiniteTor Λ.X X.obj.left :=
  ⟨K.obj ⊗ L.obj, ((stability D₀ ell hne Λ hΛ (𝟙 X)).2.2.2.2.1 K L).1⟩

/-- Exceptional composition is the mate of the fixed support compositor.
Source: correspondence proof, composition (blueprint: sk-thm-sf-kunneth-verdier). -/
def exceptionalComp {X Y Z : SepFinType D₀.k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    exceptional D₀ ell hne Λ hΛ (f ≫ g) ≅
      exceptional D₀ ell hne Λ hΛ g ⋙ exceptional D₀ ell hne Λ hΛ f :=
  (conjugateIsoEquiv (adjunction D₀ ell hne Λ hΛ (f ≫ g))
    ((adjunction D₀ ell hne Λ hΛ f).comp (adjunction D₀ ell hne Λ hΛ g)))
    (supportComp D₀ ell hne Λ hΛ f g)

set_option maxHeartbeats 1600000 in
-- The normalized derived-functor transports elaborate several large closed-category instances.
/-- The counit-compatible identification f! omega_Y = omega_X.
Source: correspondence proof, dualizing composition
(blueprint: sk-thm-sf-kunneth-verdier). -/
def omegaComp {X Y : SepFinType D₀.k} (f : X ⟶ Y) :
    (exceptional D₀ ell hne Λ hΛ f).obj (omega D₀ ell hne Λ hΛ Y) ≅
      omega D₀ ell hne Λ hΛ X :=
  ((exceptionalComp D₀ ell hne Λ hΛ f (structureMap D₀ Y)).app (unit D₀ Λ)).symm ≪≫
    eqToIso (congrArg (fun a : X ⟶ ProductComparisons.base D₀.k ↦
      (exceptional D₀ ell hne Λ hΛ a).obj (unit D₀ Λ))
      (by
        apply ObjectProperty.hom_ext
        exact Over.mkIdTerminal.hom_ext _ _))

/-- Exceptional tensor pairing is adjoint to inverse projection followed by the
exceptional counit. Source: proof, exceptional Hom exchange
(blueprint: sk-thm-sf-kunneth-verdier). -/
def exceptionalPairing {X Y : SepFinType D₀.k} (f : X ⟶ Y)
    (B Q : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left) :
    tensorObject D₀ ell hne Λ hΛ X ((exceptional D₀ ell hne Λ hΛ f).obj B)
        ((pull D₀ ell hne Λ hΛ f).obj Q) ⟶
      (exceptional D₀ ell hne Λ hΛ f).obj (tensorObject D₀ ell hne Λ hΛ Y B Q) :=
  (adjunction D₀ ell hne Λ hΛ f).homEquiv _ _
    (projectionInverse D₀ ell hne Λ hΛ f
        ((exceptional D₀ ell hne Λ hΛ f).obj B) Q ≫
      ⟨((adjunction D₀ ell hne Λ hΛ f).counit.app B).hom ⊗ₘ 𝟙 Q.obj⟩)

/-- The canonical exceptional internal-Hom arrow, on constructible test objects.
Source: proof, the projection/closed-adjunction Hom chain
(blueprint: sk-thm-sf-kunneth-verdier). -/
def homExchange {X Y : SepFinType D₀.k} (f : X ⟶ Y)
    (K L : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left) :
    (exceptional D₀ ell hne Λ hΛ f).obj (homObject D₀ ell hne Λ hΛ Y K L) ⟶
      homObject D₀ ell hne Λ hΛ X ((pull D₀ ell hne Λ hΛ f).obj K)
        ((exceptional D₀ ell hne Λ hΛ f).obj L) :=
  ⟨MonoidalClosed.curry
    ((RelativeKunneth.symmetry Λ X.obj.left
      ((pull D₀ ell hne Λ hΛ f).obj K).obj
      ((exceptional D₀ ell hne Λ hΛ f).obj (homObject D₀ ell hne Λ hΛ Y K L)).obj).hom ≫
    (exceptionalPairing D₀ ell hne Λ hΛ f (homObject D₀ ell hne Λ hΛ Y K L) K).hom ≫
    ((exceptional D₀ ell hne Λ hΛ f).map
      ⟨(RelativeKunneth.symmetry Λ Y.obj.left ((ihom K.obj).obj L.obj) K.obj).hom ≫
        (ihom.ev K.obj).app L.obj⟩).hom)⟩


open ProductComparisons

set_option maxHeartbeats 1600000 in
-- The normalized derived-functor transports elaborate several large closed-category instances.
/-- The assertion that the recorded alpha, beta and kappa are isomorphisms and
natural in their complex variables. Naturality is written in the ambient derived
categories; the constructible categories are full subcategories.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/_section.md, General form
(blueprint: sk-thm-sf-kunneth-verdier). -/
def Comparisons (Λ : ScalarSixRing.{u})
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hne : ringChar D.k ≠ ell)
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X) : Prop :=
  let S : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y)
      (c : Compactification f.hom.left), SixOperationsLocalizingAdjunction Λ.X c :=
    modelAdjunction D ell hne Λ hΛ
  let K := maps Λ D ell hne hΛ S
  (∀ (G : Geometry D.k) (c : Models G)
    (L₁ : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
    (L₂ : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left),
    IsIso (K.2.1 G c L₁ L₂)) ∧
  (∀ (G : Geometry D.k) (c : Models G)
    (L₁ L₁' : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
    (L₂ L₂' : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left)
    (l₁ : L₁ ⟶ L₁') (l₂ : L₂ ⟶ L₂'),
    let e₁ := ProductComparisons.exceptional Λ (S G.f₁ c.f₁)
    let e₂ := ProductComparisons.exceptional Λ (S G.f₂ c.f₂)
    let e := ProductComparisons.exceptional Λ (S (G.q ≫ G.v) c.relative.total)
    ((P Λ.X G.r₁.hom.left).map (e₁.map l₁).hom ⊗ₘ
      (P Λ.X G.r₂.hom.left).map (e₂.map l₂).hom) ≫ (K.2.1 G c L₁' L₂').hom =
    (K.2.1 G c L₁ L₂).hom ≫
      (e.map ⟨(P Λ.X G.t₁.hom.left).map l₁.hom ⊗ₘ
        (P Λ.X G.t₂.hom.left).map l₂.hom⟩).hom) ∧
  (∀ (G : Geometry D.k)
    (E₁ L₁ : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
    (E₂ L₂ : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left),
    IsIso (K.2.2.1 G E₁ L₁ E₂ L₂)) ∧
  (∀ (G : Geometry D.k)
    (E₁ E₁' L₁ L₁' : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
    (E₂ E₂' L₂ L₂' : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left)
    (e₁ : E₁' ⟶ E₁) (l₁ : L₁ ⟶ L₁') (e₂ : E₂' ⟶ E₂) (l₂ : L₂ ⟶ L₂'),
    let h₁ := (ihom E₁.obj).map l₁.hom ≫ (MonoidalClosed.pre e₁.hom).app L₁'.obj
    let h₂ := (ihom E₂.obj).map l₂.hom ≫ (MonoidalClosed.pre e₂.hom).app L₂'.obj
    ((P Λ.X G.t₁.hom.left).map h₁ ⊗ₘ (P Λ.X G.t₂.hom.left).map h₂) ≫
        K.2.2.1 G E₁' L₁' E₂' L₂' =
      K.2.2.1 G E₁ L₁ E₂ L₂ ≫
        (ihom ((P Λ.X G.t₁.hom.left).obj E₁.obj ⊗
          (P Λ.X G.t₂.hom.left).obj E₂.obj)).map
            ((P Λ.X G.t₁.hom.left).map l₁.hom ⊗ₘ
              (P Λ.X G.t₂.hom.left).map l₂.hom) ≫
        (MonoidalClosed.pre ((P Λ.X G.t₁.hom.left).map e₁.hom ⊗ₘ
          (P Λ.X G.t₂.hom.left).map e₂.hom)).app _) ∧
  (∀ (X Y W : SepFinType D.k) (pX : W ⟶ X) (pY : W ⟶ Y)
    (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)
    (c : Models (verdierGeometry X Y W pX pY sq))
    (U : ConstantModelConstructibleFiniteTor Λ.X (Spec (.of D.k)))
    (eU : U.obj ≅ 𝟙_ (CompactificationReindexing.D Λ.X (Spec (.of D.k))))
    (M : ConstantModelConstructibleFiniteTor Λ.X X.obj.left)
    (N : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left),
    IsIso (K.2.2.2 X Y W pX pY sq c U eU M N)) ∧
  (∀ (X Y W : SepFinType D.k) (pX : W ⟶ X) (pY : W ⟶ Y)
    (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)
    (c : Models (verdierGeometry X Y W pX pY sq))
    (U : ConstantModelConstructibleFiniteTor Λ.X (Spec (.of D.k)))
    (eU : U.obj ≅ 𝟙_ (CompactificationReindexing.D Λ.X (Spec (.of D.k))))
    (M M' : ConstantModelConstructibleFiniteTor Λ.X X.obj.left)
    (N N' : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left)
    (m : M ⟶ M') (n : N' ⟶ N),
    let G := verdierGeometry X Y W pX pY sq
    let omega := ((ProductComparisons.exceptional Λ (S G.f₂ c.f₂)).obj U).obj
    let e := ProductComparisons.exceptional Λ (S (G.q ≫ G.v) c.relative.total)
    ((P Λ.X pX.hom.left).map m.hom ⊗ₘ
      (P Λ.X pY.hom.left).map ((MonoidalClosed.pre n.hom).app omega)) ≫
        K.2.2.2 X Y W pX pY sq c U eU M' N' =
      K.2.2.2 X Y W pX pY sq c U eU M N ≫
        (ihom ((P Λ.X pY.hom.left).obj N.obj)).map (e.map m).hom ≫
        (MonoidalClosed.pre ((P Λ.X pY.hom.left).map n.hom)).app _)

set_option maxHeartbeats 1600000 in
-- The normalized derived-functor transports elaborate several large closed-category instances.
/-- The canonical comparisons are invertible and natural, and their constructible
exceptional-Hom specialization is invertible. The extra conjuncts spell out the
canonical kappa and the Hom exchange used in the correspondence assertion.
Source: latest blueprint, sk-thm-sf-kunneth-verdier, General form and proof
(blueprint: sk-thm-sf-kunneth-verdier).

Proof. For finite coefficients, alpha is exceptional external Kunneth. For beta,
write constructible generators as Rh_!F with F finite free lisse on a smooth
stratum. Adjunction, projection, ordinary external Kunneth and evaluation identify
the two Hom functors on products of these generators. Exactness in every argument
and thick devissage extend this to all finite-Tor constructible inputs. Apply beta
to the dualizing objects and alpha to their structure maps to obtain external
Verdier duality; evaluation and biduality identify kappa with their composite.
For the exceptional Hom exchange, test only on constructible objects T. Closed
adjunction identifies Hom(T,f!Hom(K,L)) with Hom(f_!T tensor K,L); inverse projection
identifies this with Hom(f_!(T tensor f*K),L); exceptional and closed adjunctions
identify it with Hom(T,Hom(f*K,f!L)). This is precisely homExchange, since its
uncurrying is inverse projection followed by the exceptional counit and evaluation.
Yoneda on the full constructible category proves invertibility. All chains are
natural and preserve the normalized evaluation maps. For integral coefficients,
reduce the prescribed maps and use derived Nakayama with uniform constructible
Tor bounds. For E, descend inputs and maps to integral lattices and devissage;
for the algebraic closure take a common finite coefficient-field stage. The
coefficient comparison laws identify the resulting arrows with the same alpha,
beta and kappa. Transport through the normalized compactification isomorphisms
and the identity composition gives the displayed kappaMap. -/
theorem coreComparisons :
    Comparisons Λ D₀ ell hne hΛ ∧
    (∀ (X Y W : SepFinType D₀.k) (pX : W ⟶ X) (pY : W ⟶ Y)
      (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)
      (M : ConstantModelConstructibleFiniteTor Λ.X X.obj.left)
      (N : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left),
      IsIso (kappaMap D₀ ell hne Λ hΛ X Y W pX pY sq M N)) ∧
    (∀ {X Y : SepFinType D₀.k} (f : X ⟶ Y)
      (K L : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left),
      IsIso (homExchange D₀ ell hne Λ hΛ f K L)) := by
  sorry

/-- The first correspondence isomorphism is literally the recorded kappa.
Source: first displayed correspondence isomorphism
(blueprint: sk-thm-sf-kunneth-verdier). -/
def externalDuality (X Y W : SepFinType D₀.k) (pX : W ⟶ X) (pY : W ⟶ Y)
    (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)
    (M : ConstantModelConstructibleFiniteTor Λ.X X.obj.left)
    (N : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left) :=
  letI := (coreComparisons D₀ ell hne Λ hΛ).2.1 X Y W pX pY sq M N
  asIso (kappaMap D₀ ell hne Λ hΛ X Y W pX pY sq M N)

/-- Exceptional Hom exchange, with the uniquely determined inverse of its canonical
arrow. Source: second correspondence isomorphism, proof Hom chain
(blueprint: sk-thm-sf-kunneth-verdier). -/
def homExchangeIso {X Y : SepFinType D₀.k} (f : X ⟶ Y)
    (K L : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left) :=
  letI := (coreComparisons D₀ ell hne Λ hΛ).2.2 f K L
  asIso (homExchange D₀ ell hne Λ hΛ f K L)


/-- A product realization and a correspondence with its Cartesian fixed square.
The two diagonal equations determine the diagonal uniquely, and the Cartesian
condition determines the fixed scheme up to its unique projection-preserving iso.
Source: correspondence and fixed-locus paragraph
(blueprint: sk-thm-sf-kunneth-verdier). -/
structure Correspondence (k : Type u) [Field k] where
  X : SepFinType k
  W : SepFinType k
  p₁ : W ⟶ X
  p₂ : W ⟶ X
  product : IsPullback p₁.hom.left p₂.hom.left X.obj.hom X.obj.hom
  delta : X ⟶ W
  delta₁ : delta.hom.left ≫ p₁.hom.left = 𝟙 X.obj.left
  delta₂ : delta.hom.left ≫ p₂.hom.left = 𝟙 X.obj.left
  C : SepFinType k
  c : C ⟶ W
  Fix : SepFinType k
  i : Fix ⟶ C
  d : Fix ⟶ X
  fixed : IsPullback i.hom.left d.hom.left c.hom.left delta.hom.left

/-- RHom(c2*K,c1!K), with the existing ordinary and exceptional functors.
Source: the definition of H_c(K) (blueprint: sk-thm-sf-kunneth-verdier). -/
def correspondenceHom (G : Correspondence D₀.k)
    (K : ConstantModelConstructibleFiniteTor Λ.X G.X.obj.left) :=
  homObject D₀ ell hne Λ hΛ G.C ((pull D₀ ell hne Λ hΛ (G.c ≫ G.p₂)).obj K)
    ((exceptional D₀ ell hne Λ hΛ (G.c ≫ G.p₁)).obj K)

/-- The ordinary composition comparison on the chosen constructible restrictions.
Source: second correspondence isomorphism
(blueprint: sk-thm-sf-kunneth-verdier). -/
def pullComp {X Y Z : SepFinType D₀.k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull D₀ ell hne Λ hΛ (f ≫ g) ≅
      pull D₀ ell hne Λ hΛ g ⋙ pull D₀ ell hne Λ hΛ f :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    ((leftDerivedUpperStarComp Λ.X f.hom.left g.hom.left).app K.obj))
    (by
      intro K L h
      ext
      exact (leftDerivedUpperStarComp Λ.X f.hom.left g.hom.left).hom.naturality h.hom)

set_option maxHeartbeats 1600000 in
-- The normalized derived-functor transports elaborate several large closed-category instances.
/-- The second correspondence iso: inverse exceptional Hom exchange, exceptional
composition, and the exceptional image of the first (kappa) iso.
Source: second displayed correspondence isomorphism
(blueprint: sk-thm-sf-kunneth-verdier). -/
def correspondenceIso (G : Correspondence D₀.k)
    (K : ConstantModelConstructibleFiniteTor Λ.X G.X.obj.left) :
    correspondenceHom D₀ ell hne Λ hΛ G K ≅
      (exceptional D₀ ell hne Λ hΛ G.c).obj (exteriorObject D₀ ell hne Λ hΛ G K) :=
  let B := (pull D₀ ell hne Λ hΛ G.p₂).obj K
  let Q := (exceptional D₀ ell hne Λ hΛ G.p₁).obj K
  let κ : exteriorObject D₀ ell hne Λ hΛ G K ≅ homObject D₀ ell hne Λ hΛ G.W B Q :=
    ObjectProperty.isoMk _ (externalDuality D₀ ell hne Λ hΛ G.X G.X G.W
      G.p₁ G.p₂ G.product K K)
  let ιC : ConstantModelConstructibleFiniteTor Λ.X G.C.obj.left ⥤ D Λ.X G.C.obj.left :=
    (constantModelBoundedConstructible Λ.X G.C.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι
  let eP : ((pull D₀ ell hne Λ hΛ (G.c ≫ G.p₂)).obj K).obj ≅
      ((pull D₀ ell hne Λ hΛ G.c).obj B).obj :=
    ιC.mapIso ((pullComp D₀ ell hne Λ hΛ G.c G.p₂).app K)
  let eQ : ((exceptional D₀ ell hne Λ hΛ (G.c ≫ G.p₁)).obj K).obj ≅
      ((exceptional D₀ ell hne Λ hΛ G.c).obj Q).obj :=
    ιC.mapIso ((exceptionalComp D₀ ell hne Λ hΛ G.c G.p₁).app K)
  let eH : (correspondenceHom D₀ ell hne Λ hΛ G K).obj ≅
      (homObject D₀ ell hne Λ hΛ G.C ((pull D₀ ell hne Λ hΛ G.c).obj B)
        ((exceptional D₀ ell hne Λ hΛ G.c).obj Q)).obj :=
    ((MonoidalClosed.internalHom.mapIso eP.symm.op).app _) ≪≫
      (ihom ((pull D₀ ell hne Λ hΛ G.c).obj B).obj).mapIso eQ
  ObjectProperty.isoMk _ eH ≪≫
    (homExchangeIso D₀ ell hne Λ hΛ G.c B Q).symm ≪≫
    (exceptional D₀ ell hne Λ hΛ G.c).mapIso κ.symm

set_option maxHeartbeats 1600000 in
-- Compositor transports elaborate the same large closed-category instances as correspondenceIso.
/-- The inverse of the second correspondence isomorphism, specified before any
invertibility proof: c! of kappa, the exceptional Hom arrow, then the inverse
ordinary/exceptional composition identifications. No inverse of a sorried
comparison occurs in this construction.
Source: second displayed isomorphism and its Hom test
(blueprint: sk-thm-sf-kunneth-verdier). -/
def correspondenceInverse (G : Correspondence D₀.k)
    (K : ConstantModelConstructibleFiniteTor Λ.X G.X.obj.left) :
    (exceptional D₀ ell hne Λ hΛ G.c).obj (exteriorObject D₀ ell hne Λ hΛ G K) ⟶
      correspondenceHom D₀ ell hne Λ hΛ G K :=
  let B := (pull D₀ ell hne Λ hΛ G.p₂).obj K
  let Q := (exceptional D₀ ell hne Λ hΛ G.p₁).obj K
  let κ : exteriorObject D₀ ell hne Λ hΛ G K ⟶ homObject D₀ ell hne Λ hΛ G.W B Q :=
    ⟨kappaMap D₀ ell hne Λ hΛ G.X G.X G.W G.p₁ G.p₂ G.product K K⟩
  let ιC : ConstantModelConstructibleFiniteTor Λ.X G.C.obj.left ⥤ D Λ.X G.C.obj.left :=
    (constantModelBoundedConstructible Λ.X G.C.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι
  let eP : ((pull D₀ ell hne Λ hΛ (G.c ≫ G.p₂)).obj K).obj ≅
      ((pull D₀ ell hne Λ hΛ G.c).obj B).obj :=
    ιC.mapIso ((pullComp D₀ ell hne Λ hΛ G.c G.p₂).app K)
  let eQ : ((exceptional D₀ ell hne Λ hΛ (G.c ≫ G.p₁)).obj K).obj ≅
      ((exceptional D₀ ell hne Λ hΛ G.c).obj Q).obj :=
    ιC.mapIso ((exceptionalComp D₀ ell hne Λ hΛ G.c G.p₁).app K)
  let eH : (correspondenceHom D₀ ell hne Λ hΛ G K).obj ≅
      (homObject D₀ ell hne Λ hΛ G.C ((pull D₀ ell hne Λ hΛ G.c).obj B)
        ((exceptional D₀ ell hne Λ hΛ G.c).obj Q)).obj :=
    ((MonoidalClosed.internalHom.mapIso eP.symm.op).app _) ≪≫
      (ihom ((pull D₀ ell hne Λ hΛ G.c).obj B).obj).mapIso eQ
  (exceptional D₀ ell hne Λ hΛ G.c).map κ ≫
    homExchange D₀ ell hne Λ hΛ G.c B Q ≫ (ObjectProperty.isoMk _ eH).inv

/-- Diagonal evaluation, transposed through the ordinary pull/direct adjunction.
Source: trace construction, e_K (blueprint: sk-thm-sf-kunneth-verdier). -/
def diagonalEvaluation (G : Correspondence D₀.k)
    (K : ConstantModelConstructibleFiniteTor Λ.X G.X.obj.left) :
    exteriorObject D₀ ell hne Λ hΛ G K ⟶
      (direct D₀ ell hne Λ hΛ G.delta).obj (omega D₀ ell hne Λ hΛ G.X) :=
  (ordinaryAdjunction D₀ ell hne Λ hΛ G.delta).homEquiv _ _
    ⟨(RelativeKunneth.pullTensor Λ G.delta.hom.left _ _).hom ≫
      (((RelativeKunneth.pullPath Λ G.delta.hom.left G.p₁.hom.left (𝟙 _) G.delta₁ K.obj) ≪≫
          (leftDerivedUpperStarId Λ.X G.X.obj.left).app K.obj).hom ⊗ₘ
        ((RelativeKunneth.pullPath Λ G.delta.hom.left G.p₂.hom.left (𝟙 _) G.delta₂
          (dual D₀ ell hne Λ hΛ G.X K).obj) ≪≫
          (leftDerivedUpperStarId Λ.X G.X.obj.left).app
            (dual D₀ ell hne Λ hΛ G.X K).obj).hom) ≫
      (ihom.ev K.obj).app (omega D₀ ell hne Λ hΛ G.X).obj⟩

/-- The same arbitrary finite commutative primary coefficients as in the source.
Source: the standing finite-coefficient convention
(blueprint: sk-thm-sf-kunneth-verdier). -/
abbrev finiteRing (A : Type) [CommRing A] [Finite A] : ScalarSixRing.{u} := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  exact CommMon.mk (Profinite.continuousMapRingObj A)

/-- Finite primary coefficients are in the recorded admissible coefficient class;
this is a coefficient condition, not an exceptional-adjoint admissibility datum.
Source: coefficient convention (blueprint: sk-thm-sf-kunneth-verdier).
Proof. Equip the finite ring with discrete topology. Its given finiteness,
commutativity and the exponent chosen from hA supply the finite coefficient
alternative in IsLocalizingAdmissibleCoefficient. The coefficient comparison
is Iso.refl, since finiteRing is exactly that discrete condensed ring. -/
theorem finiteAdmissible (A : Type) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0) :
    IsLocalizingAdmissibleCoefficient ell (finiteRing A).X := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨hA.choose, hA.choose_spec.2⟩, ⟨Iso.refl _⟩⟩

set_option maxHeartbeats 1600000 in
-- The normalized derived-functor transports elaborate several large closed-category instances.
end AlgebraicGeometry.ProEtale.CondensedRing.KunnethVerdier
