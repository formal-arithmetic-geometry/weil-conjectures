/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.RepresentationTheory.LAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GaloisLisseRepresentations
public import WeilConjectures.AlgebraicGeometry.EtaleWeilFundamentalRepresentation
public import WeilConjectures.AlgebraicGeometry.LisseIntegralSmallCoefficients
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
public import WeilConjectures.AlgebraicGeometry.FibreFunctorBasepointTransportData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.AlgebraicGeometry.ProEtaleWContractibleSectionsExact
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.WeilObject.Sheaf.Stalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.FibreFunctorBasepointTransport
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import Mathlib.AlgebraicGeometry.Noetherian


/-! # Condensed lisse monodromy, with finite-level normalization

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-finite/`
`thm-lisse-qlbar-representations.md`, theorem and clauses (1)--(5), and Weil II (1.1.6).
(blueprint: lem-a1-condensed-lisse-monodromy).

## Main definitions

* `Lisse` and `fibre`: the existing lisse full subcategory and its actual geometric fibre.
* `Model` and `ModelNormalization`: integral coefficient models and finite-level normalization.
* `Comparison` and `CompatibleSystem`: the exact tensor comparison and its compatibilities.
* `WeilCompatibility`: equality of the path-defined degree-one operators.

## Main statement

* `condensed_lisse_monodromy`: existence and fibre-compatible uniqueness of the comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseMonodromy

/-- The same algebraic closure in the module-value universe, using only a size lift.
Source: the coefficient convention of `thm-lisse-qlbar-representations`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
abbrev Coeff (l : ℕ) [Fact l.Prime] := ULift.{u + 1} (PadicAlgCl l)

/-- The canonical algebraic-closure structure on the size lift.
Source: Mathlib's transport of algebraic closedness and algebraicity along equivalences.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
instance coeffClosure (l : ℕ) [Fact l.Prime] : IsAlgClosure ℚ_[l] (Coeff.{u} l) where
  isAlgClosed := ⟨fun f ↦ by
    have h := (IsAlgClosed.splits (f.map ULift.ringEquiv.toRingHom)).map
      (ULift.ringEquiv : Coeff.{u} l ≃+* PadicAlgCl l).symm.toRingHom
    simpa only [Polynomial.map_map, RingEquiv.symm_toRingHom_comp_toRingHom,
      Polynomial.map_id] using h⟩
  isAlgebraic := (ULift.algEquiv (R := ℚ_[l]) (A := PadicAlgCl l)).symm.isAlgebraic

/-- The full category of locally finite free modules over precisely p_X^* Qbar_l.
Source: `sk-lem-coefficient-heart`, introductory lisse clause.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
abbrev Lisse (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (X := X))

/-- The ambient internal module category; this abbreviation introduces no new coefficients.
Source: `sk-def-sfb-pulled-back-coefficients`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
abbrev Modules (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj l) X)

/-- The published terminal-section evaluation, with its scalar size transport specified.
Source: the Fibres paragraph of `thm-lisse-qlbar-representations`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def geometricEvaluation (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    Modules l (Spec (.of Ω)) ⥤ ModuleCat.{u + 1} (Coeff.{u} l) :=
  CondensedQbarGeometricEvaluation.fieldFiber Ω l ⋙
    ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : Coeff.{u} l →+* PadicAlgCl l)

/-- Gamma(Spec Omega, x^* -), with the canonical size transport on scalar modules.
Source: `thm-lisse-qlbar-representations`, Fibres paragraph.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def rawFibre (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Modules l X ⥤ ModuleCat.{u + 1} (Coeff.{u} l) :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj l) x ⋙ geometricEvaluation l Ω

/-- The displayed fibre functor restricted to lisse objects.
Source: `thm-lisse-qlbar-representations`, theorem.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def fibre (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Lisse l X ⥤ ModuleCat.{u + 1} (Coeff.{u} l) :=
  ObjectProperty.ι (IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (X := X)) ⋙
    rawFibre l x

/-- The allowed geometric domains, retaining their given k-structure.
Source: the hypotheses of `lem-a1-condensed-lisse-monodromy`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure Domain (k : Type u) [Field k] where
  X : Scheme.{u}
  overBase : X.Over (Spec (.of k))
  connected : ConnectedSpace X
  regular : IsRegular X
  finiteType : LocallyOfFiniteType (X ↘ Spec (.of k))
  quasiCompact : QuasiCompact (X ↘ Spec (.of k))
  separated : IsSeparated (X ↘ Spec (.of k))

attribute [instance] Domain.overBase Domain.connected Domain.regular Domain.finiteType
  Domain.quasiCompact Domain.separated

/-- The actual abelian geometric fibre, before equipping it with constant scalars.
Source: the Fibres paragraph of `thm-lisse-qlbar-representations`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def abFibre {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  ProEtale.upperStar Ab.{u + 1} x ⋙ Sheaf.Γ _ Ab.{u + 1}

/-- The canonical forgetting comparison for comparison inverse image, retaining its unit.
Source: finite comparison in `thm-lisse-qlbar-representations` (1).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure ForgetComparison (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] where
  iso : supportSiteComparisonCoefficientPullback (ModuleCat.{u + 1} R) X ⋙
      sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ≅
    sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ⋙
      supportSiteComparisonCoefficientPullback Ab.{u + 1} X
  unit : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (U : X.Etale)
    (s : F.obj.obj (op U)),
    ((iso.hom.app F).hom.app (op ((Scheme.toProEt X).obj U)))
      (((supportSiteComparisonCoefficientAdjunction (ModuleCat.{u + 1} R) X).unit.app F).hom.app
        (op U) s) =
      ((supportSiteComparisonCoefficientAdjunction Ab.{u + 1} X).unit.app
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).obj F)).hom.app (op U) s

/-- Insert the published underlying-sheaf equality without unfolding scalar extension.
Source: `finiteCoefficientModEquivalence_functor_comp_sheafCompose`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
@[irreducible] def finiteUnderlyingIso (X : Scheme.{u}) (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] [Finite R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj R) X)) :
    M.X ≅ (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1})).obj
        ((finiteCoefficientModEquivalence X R).functor.obj M) :=
  eqToIso (congrArg (fun F ↦ F.obj M)
    (finiteCoefficientModEquivalence_functor_comp_sheafCompose X R)).symm

/-- Finite geometric fibres and finite paths with their germ rules. These rules, rather
than an arbitrary stalk isomorphism, specify both comparisons uniquely.
Source: `cor-galois-lisse-representations` (1), finite-fibre normalization.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure FiniteNormalization (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) where
  point : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    (abFibre x).obj ((supportSiteComparisonCoefficientPullback Ab.{u + 1} X).obj F) ≅
      (pointSmallEtale x).ulift.{u + 1}.sheafFiber.obj F
  point_germ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (U : X.Etale) (a : (pointSmallEtale x).fiber.obj U)
    (t : Scheme.ProEt.mk (𝟙 (Spec (.of Ω))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ x).obj ((Scheme.toProEt X).obj U))
    (_ : t.left ≫ pullback.fst U.hom x = a.left) (s : F.obj.obj (op U)),
    (point Ω x).hom
      (ProEtale.germ Ab.{u + 1} x _ t
        (((supportSiteComparisonCoefficientAdjunction Ab.{u + 1} X).unit.app F).hom.app
          (op U) s)) =
      (pointSmallEtale x).ulift.{u + 1}.toPresheafFiber U ⟨a⟩ F.obj s
  path : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X) (_τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y),
    (pointSmallEtale x).ulift.{u + 1}.sheafFiber.obj F ≅
      (pointSmallEtale y).ulift.{u + 1}.sheafFiber.obj F
  path_germ : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X) (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y)
    (P : X.FiniteEtale) (a : (FiniteEtale.fiber x).obj P) (s : F.obj.obj (op P.obj)),
    (path Ω Ω' x y τ).hom
      ((pointSmallEtale x).ulift.{u + 1}.toPresheafFiber P.obj ⟨a⟩ F.obj s) =
      (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber P.obj ⟨τ.hom.app P a⟩ F.obj s

set_option maxHeartbeats 1000000 in
-- The finite-reduction comparison involves several nested sheaf and scalar-extension functors.
/-- A finite coefficient model with an actual lisse integral lattice. The ell-power
reductions form a cofinal subsystem of the uniformizer-power reductions.
Source: `thm-lisse-qlbar-representations` (1)--(4).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure Model (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (L : Lisse l X) where
  E : PadicAlgCl.FiniteIntermediateField l
  rational : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicSubfieldRingObj X l E)
  integral : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X)
  rational_lisse : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) rational
  integral_lisse : IsLisseCoefficientModule (Profinite.padicIntegersRingObj l E.1) integral
  rationalization : (Mod.extendScalars (padicIntegersToPadicSubfield X l E)).obj integral ≅
    rational
  scalarExtension : (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X l E)).obj
    rational ≅ L.obj
  inclusion_mono : Mono
    ((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X l E)).unit.app integral ≫
      (Mod.comap (padicIntegersToPadicSubfield X l E)).map rationalization.hom)
  finite : ∀ n : ℕ, LisseModuleSheafCategory X
    (ULift.{u + 1} (PadicAlgCl.integersModPow l E.1 (n + 1)))
  reduction : ∀ n : ℕ,
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow l E.1 (n + 1))).functor.obj
      ((Mod.extendScalars (integersModPowReduction X l E.1 (n + 1))).obj integral) ≅
        (supportSiteComparisonCoefficientPullback
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (PadicAlgCl.integersModPow l E.1 (n + 1)))) X).obj (finite n).obj
  /-- The actual compatible finite reductions, on underlying abelian sheaves. -/
  diagram : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u + 1}
  level : ∀ n : ℕ, diagram.obj (op n) ≅
    (sheafCompose _ (forget₂
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersModPow l E.1 (n + 1))))
        Ab.{u + 1})).obj (finite n).obj
  completion : Cone (diagram ⋙ supportSiteComparisonCoefficientPullback Ab.{u + 1} X)
  completion_point : completion.pt = integral.X
  completion_limit : IsLimit completion

  forgetComparison : ∀ n : ℕ, ForgetComparison X
    (ULift.{u + 1} (PadicAlgCl.integersModPow l E.1 (n + 1)))
  completion_projection : ∀ n : ℕ,
    eqToHom completion_point.symm ≫ completion.π.app (op n) =
      Mod.extendUnitHom (integersModPowReduction X l E.1 (n + 1)) integral ≫
        (finiteUnderlyingIso X (PadicAlgCl.integersModPow l E.1 (n + 1))
          ((Mod.extendScalars (integersModPowReduction X l E.1 (n + 1))).obj integral)).hom ≫
        (sheafCompose _ (forget₂
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (PadicAlgCl.integersModPow l E.1 (n + 1)))) Ab.{u + 1})).map (reduction n).hom ≫
        (forgetComparison n).iso.hom.app (finite n).obj ≫
        (supportSiteComparisonCoefficientPullback Ab.{u + 1} X).map (level n).inv
  normalization : ∀ n : ℕ, FiniteNormalization X (diagram.obj (op n))
  point_completion : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    IsLimit ((abFibre x).mapCone completion)

/-- The actual lattice inclusion followed by localization and coefficient extension.
Source: `thm-lisse-qlbar-representations` (1)--(3).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def Model.inclusion (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} {L : Lisse l X}
    (M : Model l X L) : M.integral.X ⟶ L.obj.X :=
  Mod.extendUnitHom (padicIntegersToPadicSubfield X l M.E) M.integral ≫
    M.rationalization.hom.hom ≫
      Mod.extendUnitHom (padicSubfieldRingObjToPadicAlgCl X l M.E) M.rational ≫
        M.scalarExtension.hom.hom

/-- The specified projection of an actual integral geometric fibre to its finite etale fibre.
Source: `thm-lisse-qlbar-representations` (1).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def Model.projection (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} {L : Lisse l X}
    (M : Model l X L) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (n : ℕ) :
    (abFibre x).obj M.integral.X ⟶
      (pointSmallEtale x).ulift.{u + 1}.sheafFiber.obj (M.diagram.obj (op n)) :=
  (abFibre x).map (eqToHom M.completion_point.symm ≫ M.completion.π.app (op n)) ≫
    ((M.normalization n).point Ω x).hom

/-- Pointwise classical comparison and its specified actual fibre identifications.
Source: `thm-lisse-qlbar-representations`, theorem, and
`cor-galois-lisse-representations` (2).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure Comparison (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsNoetherian X] [X.IsSeparated] [∀ z : X, Invertible (l : X.residueField z)] where
  classicalPaths : AdicFibrePathTransport l X (Coeff.{u} l)
  equivalence : Lisse l X ≌ LisseAlgebraicSheaf l X (Coeff.{u} l)
  /-- Exactness refers also to the inherited sheaf exact structure. -/
  preadditive : Preadditive (LisseAlgebraicSheaf l X (Coeff.{u} l))
  additive : @Functor.Additive _ _ _ _ _ preadditive equivalence.functor
  limits : PreservesFiniteLimits equivalence.functor
  colimits : PreservesFiniteColimits equivalence.functor
  fibreIso : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    equivalence.functor ⋙ lisseAlgebraicFiberFunctor l X x (Coeff.{u} l) ≅ fibre l x
  sheafExact : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (A B C : Lisse l X) (f : A ⟶ B) (g : B ⟶ C),
    imageSubobject f.hom = kernelSubobject g.hom →
      imageSubobject ((fibre l x).map f) = kernelSubobject ((fibre l x).map g)
  /-- The tensor structure on the full subcategory is the ambient module tensor. -/
  monoidal : MonoidalCategory (Lisse l X)
  inclusionMonoidal : @Functor.Monoidal (Lisse l X) _ monoidal (Modules l X) _ _
    (ObjectProperty.ι _)
  classicalMonoidal : MonoidalCategory (LisseAlgebraicSheaf l X (Coeff.{u} l))
  tensorFormula : ∀ A B : Lisse l X,
    (@MonoidalCategory.tensorObj _ _ monoidal.toMonoidalCategoryStruct A B).obj =
      (Mod.tensorLeft B.obj).obj A.obj
  unitFormula : (@MonoidalCategory.tensorUnit _ _ monoidal.toMonoidalCategoryStruct).obj =
    Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) X)
  classicalTensorFormula : ∀ A B : LisseAlgebraicSheaf l X (Coeff.{u} l),
    @MonoidalCategory.tensorObj _ _ classicalMonoidal.toMonoidalCategoryStruct A B =
      lisseAlgebraicTensor l X (Coeff.{u} l) A B
  classicalUnitFormula :
    @MonoidalCategory.tensorUnit _ _ classicalMonoidal.toMonoidalCategoryStruct =
    lisseAlgebraicUnit l X (Coeff.{u} l)
  monoidalComparison : @Functor.Monoidal _ _ monoidal _ _ classicalMonoidal
    equivalence.functor
  fibreMonoidal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    @Functor.Monoidal (Lisse l X) _ monoidal _ _ _ (fibre l x)
  classicalFibreMonoidal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X),
    @Functor.Monoidal (LisseAlgebraicSheaf l X (Coeff.{u} l)) _ classicalMonoidal
      _ _ _ (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l))
  fibreIsoMonoidal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X),
    @NatTrans.IsMonoidal _ _ monoidal _ _ _ _ _ (fibreIso Ω x).hom
      (@Functor.LaxMonoidal.comp _ _ monoidal _ _ classicalMonoidal _ _ _
        equivalence.functor (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l))
        monoidalComparison.toLaxMonoidal (classicalFibreMonoidal Ω x).toLaxMonoidal)
      (fibreMonoidal Ω x).toLaxMonoidal



/-- Its actual classical fibre identification, with the published object equality inserted.
Source: the actual-fibre formula of `def-pod-lisse-l-adic-sheaves`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def Comparison.beta (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    [IsNoetherian X] [X.IsSeparated] [∀ z : X, Invertible (l : X.residueField z)]
    (C : Comparison l X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (L : Lisse l X) :
    (fibre l x).obj L ≃ₗ[Coeff.{u} l]
      lisseAlgebraicFiber l X (Coeff.{u} l) x (C.equivalence.functor.obj L) :=
  ((C.fibreIso Ω x).symm.app L ≪≫
    eqToIso (lisseAlgebraicFiberFunctor_obj l X x (Coeff.{u} l)
      (C.equivalence.functor.obj L))).toLinearEquiv

/-- The canonical finite-set path, including geometric points with different fields.
Source: the finite-cover stalk transport of `def-galois-fibre-functor`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def flcPath {X : Scheme.{u}} {Ω Ω' : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω') ⟶ X}
    (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y) : flcFiber x ≅ flcFiber y :=
  NatIso.ofComponents (fun F ↦ (FiniteLocallyConstant.transport x y τ F).toIso)
    (fun f ↦ ConcreteCategory.hom_ext _ _ fun v ↦
      (FiniteLocallyConstant.sheafFiber_map_transport x y τ f v).symm)

/-- Transport on the displayed condensed fibre, obtained from the normalized classical path.
Source: finite-path normalization in `def-wf-fundamental-representation`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def Comparison.path (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    [IsNoetherian X] [X.IsSeparated] [∀ z : X, Invertible (l : X.residueField z)]
    (C : Comparison l X) {Ω Ω' : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω') ⟶ X}
    (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y)
    (L : Lisse l X) : (fibre l x).obj L ≃ₗ[Coeff.{u} l] (fibre l y).obj L :=
  ((C.fibreIso Ω x).symm.app L ≪≫
    (C.classicalPaths.algebraic.map x y (flcPath τ)).app (C.equivalence.functor.obj L) ≪≫
      (C.fibreIso Ω' y).app L).toLinearEquiv

/-- The abelian fibre and the displayed coefficient-module fibre are identified by
module pullback and evaluation at the terminal object, with no chosen isomorphism.
Source: `thm-lisse-qlbar-representations`, Fibres paragraph.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def rawAbIso (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) (M : Modules l X) :
    (abFibre x).obj M.X ≅
      (forget₂ (ModuleCat.{u + 1} (Coeff.{u} l)) Ab.{u + 1}).obj ((rawFibre l x).obj M) :=
  (Sheaf.Γ _ Ab.{u + 1}).mapIso
    (CondensedRing.upperStarObjXIso (Profinite.padicAlgClRingObj l) x M).symm ≪≫
      (Sheaf.ΓNatIsoSheafSections _ Ab.{u + 1}
        (Scheme.ProEt.isTerminalMkId (Spec (.of Ω)))).app _

/-- The coefficient-module fibre of the actual inclusion of a chosen lattice.
Source: finite-model normalization in `thm-lisse-qlbar-representations` (1)--(3).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def Model.fibreInclusion (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} {L : Lisse l X}
    (M : Model l X L) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    (abFibre x).obj M.integral.X ⟶
      (forget₂ (ModuleCat.{u + 1} (Coeff.{u} l)) Ab.{u + 1}).obj ((fibre l x).obj L) :=
  (abFibre x).map (M.inclusion l) ≫ (rawAbIso l x L.obj).hom

/-- All finite-model and lattice choices give the same path action on the actual fibre.
The spanning clause is precisely localization followed by extension of coefficients.
Source: `thm-lisse-qlbar-representations` (1)--(3), integral inverse-limit formula.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure ModelNormalization (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    [IsNoetherian X] [X.IsSeparated] [∀ z : X, Invertible (l : X.residueField z)]
    (C : Comparison l X) {L : Lisse l X} (M : Model l X L) where
  spanning : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    @Submodule.span (Coeff.{u} l) ((fibre l x).obj L) _ _ _
      (Set.range (fun v ↦ M.fibreInclusion l x v)) = ⊤
  integralPath : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X) (_τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y),
    (abFibre x).obj M.integral.X ≅ (abFibre y).obj M.integral.X
  finite_projection : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X) (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y)
    (n : ℕ) (v : (abFibre x).obj M.integral.X),
    M.projection l y n ((integralPath Ω Ω' x y τ).hom v) =
      ((M.normalization n).path Ω Ω' x y τ).hom (M.projection l x n v)
  scalar_extension : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X) (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y)
    (v : (abFibre x).obj M.integral.X),
    C.path l τ L (M.fibreInclusion l x v) =
      M.fibreInclusion l y ((integralPath Ω Ω' x y τ).hom v)

/-- Domains with their derived absolute finiteness and invertibility structures.
These are conclusions of the theorem, not extra restrictions on a domain.
Source: finite-type-over-a-field hypotheses of the node.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure Context (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] extends Domain k where
  noetherian : IsNoetherian X
  absoluteSeparated : X.IsSeparated
  invertible : ∀ z : X, Invertible (l : X.residueField z)

attribute [instance] Context.noetherian Context.absoluteSeparated Context.invertible

attribute [local irreducible] CondensedRing.upperStar geometricEvaluation in
/-- Canonical fibre comparison for any scheme map, before restricting to lisse objects.
Source: the composition comparison of `sk-def-sfb-module-pushforward-pullback`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def rawPullbackFibre (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f ⋙ rawFibre l y ≅
      rawFibre l (y ≫ f) :=
  (Functor.associator (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) y) (geometricEvaluation l Ω)).symm ≪≫
      Functor.isoWhiskerRight
        (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) y f).symm
        (geometricEvaluation l Ω)

/-- Coefficient reduction along an actual continuous finite quotient of O_E.
This includes every O_E/(varpi^n), not just the cofinal ell-power quotients.
Source: clause (1) of `thm-lisse-qlbar-representations`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def finiteReductionMap (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (f : PadicAlgCl.integers l E.1 →+* R) (hf : Continuous f) :
    condensedRingObj (Profinite.padicIntegersRingObj l E.1) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj R) X :=
  coefficientMap ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap f hf)) X

/-- The actual reduction morphism preserves the coefficient-ring multiplication and unit.
Source: the coefficient changes in `thm-lisse-qlbar-representations` (1).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
instance finiteReductionMap_isMonHom (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (f : PadicAlgCl.integers l E.1 →+* R) (hf : Continuous f) :
    IsMonHom (finiteReductionMap l X E R f hf) := by
  dsimp only [finiteReductionMap, coefficientMap]
  infer_instance

/-- Base change of a finite path, allowing different fields at the two geometric points.
Source: the fibre-product projection formula of `lem-galois-pi1-functoriality`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def schemePath {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω Ω' : Type u}
    [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    {x : Spec (.of Ω) ⟶ Y} {y : Spec (.of Ω') ⟶ Y}
    (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y) :
    FiniteEtale.fiber (x ≫ f) ≅ FiniteEtale.fiber (y ≫ f) :=
  (FiniteEtale.pullbackFiberIso f x).symm ≪≫
    Functor.isoWhiskerLeft (FiniteEtale.pullback f) τ ≪≫ FiniteEtale.pullbackFiberIso f y

/-- The simultaneous comparisons and closure under actual module pullback.
Source: the theorem and pullback clauses of `lem-a1-condensed-lisse-monodromy`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure System (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] where
  comparison : ∀ D : Context l k, Comparison l D.X
  pullback_lisse : ∀ (D E : Context l k) (f : E.X ⟶ D.X) (L : Lisse l D.X),
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj L.obj)

/-- Restriction of the given module inverse image to lisse objects; f need not be k-linear.
Source: the pullback clause of `lem-a1-condensed-lisse-monodromy`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def System.pullback (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] (S : System l k)
    {D E : Context l k} (f : E.X ⟶ D.X) : Lisse l D.X ⥤ Lisse l E.X where
  obj L := ⟨(CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj L.obj,
    S.pullback_lisse D E f L⟩
  map φ := ⟨(CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map φ.hom⟩

/-- The actual composition comparison on lisse geometric fibres.
Source: `sk-def-sfb-module-pushforward-pullback`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def System.pullbackFibre (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] (S : System l k)
    {D E : Context l k} (f : E.X ⟶ D.X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ E.X) :
    S.pullback l f ⋙ fibre l y ≅ fibre l (y ≫ f) :=
  Functor.isoWhiskerLeft (ObjectProperty.ι _) (rawPullbackFibre l f y)


/-- The classical scheme inverse image specified through the normalized fibre equivalences.
The canonical comparison below fixes it up to the unique fibre-compatible isomorphism.
Source: the classical pullback clause of `lem-a1-condensed-lisse-monodromy`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def System.classicalPullback (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (S : System l k) {D E : Context l k} (f : E.X ⟶ D.X) :
    LisseAlgebraicSheaf l D.X (Coeff.{u} l) ⥤ LisseAlgebraicSheaf l E.X (Coeff.{u} l) :=
  (S.comparison D).equivalence.inverse ⋙ S.pullback l f ⋙
    (S.comparison E).equivalence.functor

/-- The specified pullback comparison, induced by the equivalence unit.
Source: the classical pullback clause of `lem-a1-condensed-lisse-monodromy`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def System.classicalPullbackIso (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (S : System l k) {D E : Context l k} (f : E.X ⟶ D.X) :
    S.pullback l f ⋙ (S.comparison E).equivalence.functor ≅
      (S.comparison D).equivalence.functor ⋙ S.classicalPullback l f :=
  Functor.isoWhiskerRight (S.comparison D).equivalence.unitIso
    (S.pullback l f ⋙ (S.comparison E).equivalence.functor)

/-- Tensor, unit and internal dual on the actual fibres, including dual morphisms.
Source: tensor and dual clauses of `lem-a1-condensed-lisse-monodromy`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure TensorDual (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    [IsNoetherian X] [X.IsSeparated] [∀ z : X, Invertible (l : X.residueField z)]
    (C : Comparison l X) where
  symmetric : @SymmetricCategory (Lisse l X) _ C.monoidal
  classicalSymmetric : @SymmetricCategory (LisseAlgebraicSheaf l X (Coeff.{u} l)) _
    C.classicalMonoidal
  inclusionBraided : @Functor.Braided (Lisse l X) _ C.monoidal symmetric.toBraidedCategory
    (Modules l X) _ _ _ (ObjectProperty.ι _)
  inclusionBraided_monoidal : inclusionBraided.toMonoidal = C.inclusionMonoidal
  comparisonBraided : @Functor.Braided (Lisse l X) _ C.monoidal symmetric.toBraidedCategory
    (LisseAlgebraicSheaf l X (Coeff.{u} l)) _ C.classicalMonoidal
      classicalSymmetric.toBraidedCategory C.equivalence.functor
  comparisonBraided_monoidal : comparisonBraided.toMonoidal = C.monoidalComparison
  fibreBraided : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    @Functor.Braided (Lisse l X) _ C.monoidal symmetric.toBraidedCategory
      (ModuleCat.{u + 1} (Coeff.{u} l)) _ _ _ (fibre l x)
  fibreBraided_monoidal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X), (fibreBraided Ω x).toMonoidal = C.fibreMonoidal Ω x
  tensor : Lisse l X → Lisse l X → Lisse l X
  tensor_object : ∀ A B, (tensor A B).obj = (Mod.tensorLeft B.obj).obj A.obj
  tensorFibre : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (A B : Lisse l X),
    (fibre l x).obj (tensor A B) ≃ₗ[Coeff.{u} l]
      ((fibre l x).obj A ⊗[Coeff.{u} l] (fibre l x).obj B)
  tensor_path : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y) (A B : Lisse l X)
    (v : (fibre l x).obj A) (w : (fibre l x).obj B),
    tensorFibre Ω' y A B
      (C.path l τ (tensor A B) ((tensorFibre Ω x A B).symm (v ⊗ₜ w))) =
      (C.path l τ A v) ⊗ₜ (C.path l τ B w)
  unit : Lisse l X
  unit_object : unit.obj = Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) X)
  unitFibre : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    (fibre l x).obj unit ≃ₗ[Coeff.{u} l] Coeff.{u} l
  unit_path : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y) (v : (fibre l x).obj unit),
    unitFibre Ω' y (C.path l τ unit v) = unitFibre Ω x v
  dual : Lisse l X → Lisse l X
  dual_object : ∀ L, (dual L).obj =
    (Mod.ihom L.obj).obj (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) X))
  dualFibre : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (L : Lisse l X),
    (fibre l x).obj (dual L) ≃ₗ[Coeff.{u} l] Module.Dual (Coeff.{u} l) ((fibre l x).obj L)
  dual_path : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y) (L : Lisse l X)
    (φ : (fibre l x).obj (dual L)) (v : (fibre l y).obj L),
    dualFibre Ω' y L (C.path l τ (dual L) φ) v =
      dualFibre Ω x L φ (C.path l τ.symm L v)
  dual_map : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (A B : Lisse l X) (f : A ⟶ B) (fdual : dual B ⟶ dual A),
    fdual.hom = eqToHom (dual_object B) ≫
      (Mod.ihomMap f.hom).app (Mod.regular
        (condensedRingObj (Profinite.padicAlgClRingObj l) X)) ≫
      eqToHom (dual_object A).symm →
    ∀ (φ : (fibre l x).obj (dual B)) (v : (fibre l x).obj A),
      dualFibre Ω x A ((fibre l x).map fdual φ) v =
        dualFibre Ω x B φ ((fibre l x).map f v)

/-- All normalized compatibility clauses. Every map of schemes is allowed, including
maps that do not commute with the displayed maps to Spec k.
Source: `lem-a1-condensed-lisse-monodromy`, all conclusions.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure CompatibleSystem (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    extends System l k where
  models : ∀ (D : Context l k) (L : Lisse l D.X), Nonempty (Model l D.X L)
  allFiniteReductions : ∀ (D : Context l k) (L : Lisse l D.X) (M : Model l D.X L)
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [Finite R]
    (f : PadicAlgCl.integers l M.E.1 →+* R) (hf : Continuous f),
    ∃ F : LisseModuleSheafCategory D.X (ULift.{u + 1} R),
      Nonempty ((finiteCoefficientModEquivalence D.X R).functor.obj
        ((Mod.extendScalars (finiteReductionMap l D.X M.E R f hf)).obj M.integral) ≅
          (supportSiteComparisonCoefficientPullback
            (ModuleCat.{u + 1} (ULift.{u + 1} R)) D.X).obj F.obj)
  normalized : ∀ (D : Context l k) (L : Lisse l D.X) (M : Model l D.X L),
    Nonempty (ModelNormalization l (comparison D) M)
  tensorDual : ∀ D : Context l k, TensorDual l (comparison D)
  classical_path : ∀ (D : Context l k) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x y : Spec (.of Ω) ⟶ D.X) (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y)
    (L : Lisse l D.X) (v : (fibre l x).obj L),
    (comparison D).beta l y L ((comparison D).path l τ L v) =
      etaleAlgebraicPath l (Coeff.{u} l) ((comparison D).equivalence.functor.obj L) τ
        ((comparison D).beta l x L v)
  pullback_path : ∀ (D E : Context l k) (f : E.X ⟶ D.X)
    (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ E.X) (y : Spec (.of Ω') ⟶ E.X)
    (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y) (L : Lisse l D.X)
    (v : (fibre l x).obj (toSystem.pullback l f |>.obj L)),
    (toSystem.pullbackFibre l f y).hom.app L
      ((comparison E).path l τ ((toSystem.pullback l f).obj L) v) =
      (comparison D).path l (schemePath f τ) L
        ((toSystem.pullbackFibre l f x).hom.app L v)
  classification : ∀ (D : Context l k) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ D.X) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    [CategoryTheory.PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber x) G],
    ∃ (c : GaloisLisseFiniteCorrespondence x G)
      (d : GaloisLisseAdicCorrespondence x G c l (Coeff.{u} l)),
    ∀ (L : Lisse l D.X) (g : G)
      (v : (d.eA.functor.obj ((comparison D).equivalence.functor.obj L)).obj.V),
      ((comparison D).fibreIso Ω x).hom.app L
        (d.τA.hom.app ((comparison D).equivalence.functor.obj L)
          ((d.eA.functor.obj ((comparison D).equivalence.functor.obj L)).obj.ρ g v)) =
      (comparison D).path l
        (CategoryTheory.PreGaloisCategory.toAutContinuousMulEquiv (FiniteEtale.fiber x) G g) L
        (((comparison D).fibreIso Ω x).hom.app L
          (d.τA.hom.app ((comparison D).equivalence.functor.obj L) v))
  automorphism : ∀ (D : Context l k) (h : D.X ≅ D.X),
    (toSystem.pullback l h.hom) ⋙ (comparison D).equivalence.functor ≅
      (comparison D).equivalence.functor ⋙
        lisseAlgebraicAutomorphismPullback h l (Coeff.{u} l)
  automorphism_fibre : ∀ (D : Context l k) (h : D.X ≅ D.X)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ D.X)
    (L : Lisse l D.X) (v : (fibre l x).obj ((toSystem.pullback l h.hom).obj L)),
    (lisseAlgebraicAutomorphismFiberIso h l (Coeff.{u} l) x
      ((comparison D).equivalence.functor.obj L)).hom
      (etaleAlgebraicFiberMap l (Coeff.{u} l) x ((automorphism D h).hom.app L)
        ((comparison D).beta l x ((toSystem.pullback l h.hom).obj L) v)) =
      (comparison D).beta l (x ≫ h.hom) L
        ((toSystem.pullbackFibre l h.hom x).hom.app L v)

/-- The classical Weil object obtained using exactly the specified pullback comparison.
Source: last clause of `lem-a1-condensed-lisse-monodromy`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def CompatibleSystem.weil (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (S : CompatibleSystem l k) (D : Context l k) (h : D.X ≅ D.X) (L : Lisse l D.X)
    (θ : (S.toSystem.pullback l h.hom).obj L ≅ L) :
    EtaleLisseWeilSheaf l (Coeff.{u} l) h :=
  Endofunctor.IsoAlgebra.mk ((S.comparison D).equivalence.functor.obj L)
    ((S.automorphism D h).symm.app L ≪≫ (S.comparison D).equivalence.functor.mapIso θ)

/-- The Weil operator comparison uses the inverse of the source path L_s and requires
no theta-stable lattice.
Source: `def-wf-fundamental-representation`, formula T_s = theta L_s^{-1}.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def WeilCompatibility (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (S : CompatibleSystem l k) : Prop :=
  ∀ (D : Context l k) (h : D.X ≅ D.X) (L : Lisse l D.X)
    (θ : (S.toSystem.pullback l h.hom).obj L ≅ L)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ D.X)
    (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber (x ≫ h.hom)) (v : (fibre l x).obj L),
    (S.comparison D).beta l x L
      ((fibre l x).map θ.hom
        ((S.toSystem.pullbackFibre l h.hom x).inv.app L
          ((S.comparison D).path l τ L v))) =
      etaleWeilFrobenius l (Coeff.{u} l) h x τ (S.weil l D h L θ)
        ((S.comparison D).beta l x L v)

/-- Geometric monodromy for the specified finite-subextension-valued condensed Qbar_l,
with the actual geometric fibre, all finite-level normalizations, arbitrary scheme pullbacks,
classical comparison, duals, and Weil operators.

Source: `thm-lisse-qlbar-representations`, theorem and clauses (1)--(5);
Weil II (1.1.6), (1.1.10).
(blueprint: lem-a1-condensed-lisse-monodromy).

Proof:

1. A field is Noetherian, and [pqf-lem-locnoeth-lft] applied to $X\to\operatorname{Spec}k$ makes
$X$ locally Noetherian. Finite type supplies quasi-compactness, so $X$ is Noetherian in the
precise sense of [thm-lisse-qlbar-representations]. Apply that theorem to the specified
pulled-back condensed coefficients and the specified geometric point. Its theorem and (3)-(5)
give the fibre equivalence and a finite coefficient model $L_E$ with a lisse lattice $L_0$. Its
(1)-(3) give, on the actual fibre, $V=\Lambda\otimes_E(M_0[1/\ell])$,
$M_0=\varprojlim_n(L_0/\varpi_E^nL_0)_{\bar x}$, with the finite actions of
[cor-galois-lisse-representations](1). In (1) the finite sheaves are read through pro-étale
inverse image, as explicitly stipulated there. Clause (2) makes this action independent of the
lattice; (3), applied to the fibre functor on integral algebraic-coefficient modules, makes it
independent of the finite model. Thus this is a canonical action on the displayed fibre, not
merely an isomorphism class of representations.

2. The tensor compatibility in [thm-lisse-qlbar-representations] and
[cor-galois-lisse-representations](1) gives the diagonal action and its associative and
symmetric constraints. The constant integral system has trivial finite actions, so its limit,
rationalization and scalar extension identify the unit with the trivial
$\Lambda$-representation. Locally $L=\Lambda_X^r$, so its sheaf dual is locally
$(\Lambda_X^r)^\vee=\Lambda_X^r$; evaluation and coevaluation are the finite basis formulas. The
geometric point module equivalence [lem-pe-point-module-pullback-equivalence] identifies these
formulas with the ordinary evaluation and coevaluation of $V$. Their tensor-natural monodromy
makes evaluation invariant. Consequently $\rho_{L^\vee}(g)\lambda=\lambda\circ\rho_L(g)^{-1}$;
this identifies the sheaf dual fibre with the contragredient and also proves compatibility with
dual morphisms.

3. The fibre functor is additive and exact on sheaf short exact sequences. The module inverse
image $\bar x^*$ is exact by [lem-sfb-derived-pullback-strong-monoidal] (its underived pullback
clause). The point $\operatorname{Spec}\Omega$ is w-contractible under
[det-pe-wlocal-strict-contractible]: its only local ring is the algebraically closed field
$\Omega$, and its component space is a singleton, hence extremally disconnected. Therefore
[det-pe-wc-sections-exact] makes evaluation there exact. This applies to internal modules by the
section-preserving equivalence [def-weil-pbc-internal-abelian-sheaf-module-equivalence].
Consequently the displayed fibre preserves sheaf short exact sequences. The fibre equivalence of
step 1 is additive (finite reduction, inverse limits and scalar extension are additive). An
additive equivalence preserves and reflects categorical kernels and cokernels by their universal
properties, so it is exact for the abelian structure transported from representations as well.

4. Let $t:F_{\bar x}\xrightarrow{\sim}F_{\bar y}$ be a finite étale fibre path. By
[lem-wf-fibre-functor-basepoint-transport] its values on the finite reductions are linear
isomorphisms $t_n$, natural in the sheaf, commuting with coefficient change and with path
composition. On $M_0$ use $(v_n)_n\mapsto(t_n(v_n))_n$, with inverse obtained from $t^{-1}$;
then invert $\ell$ and extend scalars to $\Lambda$. Naturality gives $t\rho_{\bar
x}(g)=\rho_{\bar y}(tgt^{-1})t$ at each finite level and therefore after these operations.
Tensor compatibility follows by applying finite-path naturality to the bilinear tensor map and
the unit, using [cor-galois-lisse-representations](1). The resulting maps are independent of
choices: over any common coefficient model they are the same compatible maps of finite
reductions, and the model and lattice identifications of
[thm-lisse-qlbar-representations](2)-(3) identify their rational scalar extensions. This also
proves identity and composition for the extended paths.

5. For $f:Y\to X$ between the stated domains, [lem-weil-pbc-continuous-locally-free-pullback]
preserves lisse objects, including $L_E$ and $L_0$. The exact monoidal module pullback of
[lem-sfb-derived-pullback-strong-monoidal] preserves the lattice inclusion, its localization and
its finite quotients: $f^*(L_0/\varpi_E^nL_0)=(f^*L_0)/\varpi_E^n f^*L_0$. The finite
étale/pro-étale comparison commutes with these pullbacks by
[lem-pe-coefficient-comparison-fixed-pullback]; internal and sectionwise inverse images agree by
[lem-sfb-internal-module-operations-transport]. The equivalence [thm-galois-lc-etale] identifies
finite locally constant set sheaves with finite étale covers, compatibly with pullback and
fibres. At a pointed fibre $\bar y$ over $\bar x$, [lem-galois-pi1-functoriality] identifies
every finite action with restriction along $f_*$. Applying (1)-(3) of
[thm-lisse-qlbar-representations] to the pulled-back lattice therefore identifies the action on
$(f^*L)_{\bar y}$ with $\rho_L\circ f_*$. This uses the theorem's limit formula on $Y$, and does
not assert that $f^*$ preserves arbitrary inverse limits. The underlying fibre isomorphism is
the composition comparison $(f\bar y)^*\cong\bar y^*f^*$ of
[sk-def-sfb-module-pushforward-pullback].

6. The pullback comparisons of step 5 respect identities and composites: at finite coefficients
their maps are the canonical fibre maps $z\mapsto\operatorname{pr}_1z$ of
[lem-galois-pi1-functoriality], whose composites are the same projection. The coefficient-module
composition comparisons are those of [sk-def-sfb-module-pushforward-pullback]. The same equality
passes through the fibre inverse limits and scalar extensions of
[thm-lisse-qlbar-representations](1)-(3). The identical argument with a finite path inserted
proves compatibility with geometric changes of base point, using step 4. None of these scheme
inverse images requires $f$ to be linear over $k$; in particular the calculation applies to
scheme automorphisms with nontrivial action on $k$.

7. Let $B_X$ be the classical fibre equivalence of [cor-galois-lisse-representations](2) and
$A_X$ the condensed one of step 1. Compose $A_X$ with a quasi-inverse to $B_X$. This gives the
asserted exact tensor equivalence, equipped with the counit fibre isomorphism
$B_XB_X^{-1}A_X\cong A_X$. Concretely, on an integral model its classical object is the system
of finite étale antecedents of $L_0/\varpi_E^nL_0$ supplied by
[thm-lisse-qlbar-representations](1), followed by the rationalization and coefficient extension
in [def-pod-lisse-l-adic-sheaves]. Their fibres are precisely the inverse limits and extensions
in step 1. The full faithfulness of both fibre equivalences makes this construction, and the
equivalence characterized by these fibre maps, unique up to the unique fibre-compatible
isomorphism. Steps 2, 4 and 5 show that those isomorphisms commute with tensor duals, finite
paths and scheme pullbacks, since at finite reductions they are the identity maps on the same
fibres.

8. Finally suppose $h:X\xrightarrow{\sim}X$ and a Weil isomorphism
$\theta:h^*L\xrightarrow{\sim}L$ are given. If $C$ denotes step 7's comparison and
$c_h:C(h^*L)\xrightarrow{\sim}h^*C(L)$ its pullback isomorphism, the classical Weil map is
$C(\theta)c_h^{-1}$. Naturality of its fibre comparison $b$ gives $b_{\bar x}\theta_{\bar
x}=\theta^{\rm cl}_{\bar x}b_{h\bar x}$ under the pullback-fibre identifications; step 4 gives
$b_{\bar x}L_s=L_s^{\rm cl}b_{h\bar x}$ for the specified finite path. Thus $b_{\bar
x}(\theta_{\bar x}L_s^{-1})=(\theta^{\rm cl}_{\bar x}(L_s^{\rm cl})^{-1})b_{\bar x}$. These are
exactly the degree-one operators of [def-wf-fundamental-representation], with the automorphism
pullback normalized by [def-wf-lisse-adic-automorphism-pullback]. Step 1 already identifies the
geometric actions. The conclusion does not require a lattice stable under $\theta$: only its
underlying geometric lisse sheaf was assigned a lattice.
-/
theorem condensed_lisse_monodromy
    (k : Type u) [Field k] [IsAlgClosed k] (p l : ℕ) (hp : 0 < p) [CharP k p]
    [Fact l.Prime] (hlp : l ≠ p) :
    (∀ D : Domain k, ∃ C : Context l k, C.toDomain = D) ∧
      ∃ S : CompatibleSystem l k, WeilCompatibility l S ∧
        ∀ (T : CompatibleSystem l k) (D : Context l k),
          ∃! e : (S.comparison D).equivalence.functor ≅
              (T.comparison D).equivalence.functor,
            ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ D.X)
              (L : Lisse l D.X),
              (lisseAlgebraicFiberFunctor l D.X x (Coeff.{u} l)).map (e.hom.app L) ≫
                ((T.comparison D).fibreIso Ω x).hom.app L =
                  ((S.comparison D).fibreIso Ω x).hom.app L := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
