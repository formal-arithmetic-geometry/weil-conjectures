/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarStandardCohomology
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckComposablePair
import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import WeilConjectures.CategoryTheory.BoundedBelowSecondFiltration
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import WeilConjectures.CategoryTheory.FilteredQuotientPageMaps
import WeilConjectures.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles

import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject
import Mathlib.Order.WithBotTop
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Algebra.Homology.UpperTruncationStepQuotient
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.CategoryTheory.CartanEilenbergTotalResolution
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.CategoryTheory.CartanEilenbergMappedTotal
import WeilConjectures.CategoryTheory.Derived.DerivedInjectiveResolutionNaturality
import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.CategoryTheory.CartanEilenbergAugmentationQuasiIso
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Mathlib.Algebra.Homology.HomologicalBicomplex
import WeilConjectures.Algebra.Homology.UpperTruncationStepSES
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.CategoryTheory.GrothendieckResolutionUnitComparison
import WeilConjectures.CategoryTheory.SpectralObjectBottomFiltration
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.ProperBaseChange.AlgebraicInverseImageOfTransport
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import WeilConjectures.CategoryTheory.RightDerivedInjectiveSequence
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Purity.PurityComparisonUnitInjectiveModel
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonBoundary
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonGlobalCohomologyFiniteNormalized
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology

/-!
# Supported cohomology in the lowest local degree

Source: Stacks Project, Tags 015N, 09XP, 09XQ and 099V
(blueprint: lem-pur-supported-bottom-gluing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u vC uC vD uD
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry WeilConjectures

namespace AlgebraicGeometry.Scheme

/-- The signed finite pro-etale line, with exactly the recorded constant-scalar restriction.
Source: coefficient-twist convention and Stacks 099R
(blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomProTwist (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u}) (a : ℤ) :=
  (finiteTateConstantRestriction l E n T).obj (finiteCoefficientTwist l E T n a)

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- Forget the scalar action, retaining the actual abelian sheaf.
Source: Stacks 03FD and the support convention
(blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomForgetEt (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- The same scalar-forgetting construction on the pro-etale site.
Source: Stacks 03FD (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomForgetPro (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- The pro-etale sheaf support kernel, in ordinary abelian sheaves.
Source: Stacks 09XP, the identical kernel construction in the other topology
(blueprint: lem-pur-supported-bottom-gluing). -/
def bottomProKernel {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  kernel (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    i.openComplement.ι).unit

/-- Evaluation of an abelian etale sheaf at an object.
Source: Stacks 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomEvalEt {X : Scheme.{u}} (U : X.Etale) :=
  sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op U)

/-- Evaluation of an abelian pro-etale sheaf at an etale object.
Source: Stacks 099R (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomEvalPro {X : Scheme.{u}} (U : X.Etale) :=
  sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op ((Scheme.toProEt X).obj U))

/-- The presheaf of cohomology of the evaluated complex. These are presheaf homology,
not sheafified homology; sheafhood is a conclusion of the bottom-degree theorem.
Source: Stacks 015N and 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomComplexPresheaf {X : Scheme.{u}}
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (d : ℕ) :=
  (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K).asFunctor ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) d

/-- Pro-etale supported groups evaluated on the etale site, before any sheafification.
Source: Stacks 099R (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomProComplexPresheaf {X : Scheme.{u}}
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) ℕ)
    (d : ℕ) :=
  (Scheme.toProEt X).op ⋙
    (((sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).asFunctor ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) d

/-- The canonical edge characterized on cocycles, together with the asserted unique gluing.
Source: Stacks 015N, lowest-row edge and the sheaf axiom
(blueprint: lem-pur-supported-bottom-gluing). -/
structure SupportedBottomEdge {X : Scheme.{u}}
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (d : ℕ) where
  edge : bottomComplexPresheaf K d ≅ (K.homology d).obj
  cycles : ∀ U : X.Etale,
    ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).asFunctor.obj (op U)).cycles d ≅
        (K.cycles d).obj.obj (op U)
  cycles_inclusion : ∀ U : X.Etale,
    (cycles U).hom ≫ (K.iCycles d).hom.app (op U) =
      ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).asFunctor.obj (op U)).iCycles d
  edge_cocycles : ∀ U : X.Etale,
    ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).asFunctor.obj (op U)).homologyπ d ≫
        edge.hom.app (op U) = (cycles U).hom ≫ (K.homologyπ d).hom.app (op U)
  gluing : Presheaf.IsSheaf X.smallEtaleTopology (bottomComplexPresheaf K d)

open CategoryTheory.MonoidalCategory
open scoped TensorProduct

/-- The recorded coefficient quotient, indexed by its positive level minus one.
The level is positive in `P`, so `(P.level - 1) + 1 = P.level`.
Source: finite coefficient conventions (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomCoefficient (P : PurityFiniteSetting.{u}) :=
  Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)

/-- The existing signed etale root line at the chosen annihilating power.
Source: Stacks 03PK (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomEtaleTwist (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ) :=
  Scheme.finiteEtaleTateSheaf (bottomCoefficient P) (P.coefficients.l ^ (r + 1)) T hA a

/-- The existing signed pro-etale root line, at exactly the same finite coefficient level.
Source: coefficient twists (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomProLine (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (a : ℤ) :=
  Scheme.bottomProTwist P.coefficients.l P.extension (P.level - 1) T a

/-- The comparison inverse image with these fixed ordinary module coefficients.
Source: Stacks 099R (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomNu (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (bottomCoefficient P)) T

/-- Evaluation on the actual etale signed line.
Source: Stacks 03EL (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomEtaleEvaluation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (b : ℕ) :
    bottomEtaleTwist P T r hA (b + 1 : ℕ) ⊗ bottomEtaleTwist P T r hA (.negSucc b) ⟶
      bottomEtaleTwist P T r hA 0 :=
  (ihom.ev (bottomEtaleTwist P T r hA (b + 1 : ℕ))).app (bottomEtaleTwist P T r hA 0)

/-- Signed coefficient comparisons, fixed by roots in nonnegative degrees and by evaluation
in negative degrees. The pullback comparisons are fixed by the same equations.
Source: Stacks 099R, 03PK and 03EL
(blueprint: lem-pur-supported-bottom-gluing). -/
structure SignedFiniteTateComparison (P : PurityFiniteSetting.{u}) where
  theta : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ),
    (bottomNu P T).obj (bottomEtaleTwist P T r hA a) ≅ bottomProLine P T a
  positive : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℕ),
    Scheme.IsFiniteTateSiteComparison P.coefficients.l P.extension (P.level - 1) T
      r hA a (theta T r hA a)
  evaluation : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))] (b : ℕ),
    bottomProLine P T (b + 1 : ℕ) ⊗ bottomProLine P T (.negSucc b) ⟶ bottomProLine P T 0
  evaluation_sections : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    (b : ℕ) (W : T.ProEtᵒᵖ) (x : (bottomProLine P T (b + 1 : ℕ)).obj.obj W)
    (f : (bottomProLine P T (.negSucc b)).obj.obj W),
    (evaluation T b).hom.app W
      ((Functor.LaxMonoidal.μ
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (bottomCoefficient P)))
        _ _).app W (x ⊗ₜ[_] f)) = f.app (op (Over.mk (𝟙 W.unop))) x
  negative : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (b : ℕ),
    (bottomNu P T).map (bottomEtaleEvaluation P T r hA b) ≫ (theta T r hA 0).hom =
      Functor.OplaxMonoidal.δ (bottomNu P T) _ _ ≫
        tensorHom (theta T r hA (b + 1 : ℕ)).hom (theta T r hA (.negSucc b)).hom ≫ evaluation T b
  pullback : ∀ (T T' : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    [T'.Over (Spec (CommRingCat.of P.field.k))] (v : T' ⟶ T)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0),
    Σ' (c : ∀ a : ℤ, (Etale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).obj
          (bottomEtaleTwist P T r hA a) ≅ bottomEtaleTwist P T' r hA a)
      (e : ∀ a : ℤ, (ProEtale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).obj
          (bottomProLine P T a) ≅ bottomProLine P T' a),
      (∀ a : ℕ, Scheme.IsFiniteTateEtalePullback P.coefficients.l P.extension (P.level - 1)
        T v r hA a (c a) ∧
        Scheme.IsFiniteTateProPullback P.coefficients.l P.extension (P.level - 1)
          T v a (e a)) ∧
      (∀ b : ℕ,
        (Etale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).map
            (bottomEtaleEvaluation P T r hA b) ≫ (c 0).hom =
          Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v)
            _ _ ≫ tensorHom (c (b + 1 : ℕ)).hom (c (.negSucc b)).hom ≫
              bottomEtaleEvaluation P T' r hA b) ∧
      (∀ b : ℕ,
        (ProEtale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).map
            (evaluation T b) ≫ (e 0).hom =
          Functor.OplaxMonoidal.δ
            (ProEtale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v) _ _ ≫
              tensorHom (e (b + 1 : ℕ)).hom (e (.negSucc b)).hom ≫ evaluation T' b) ∧
      (∀ a : ℤ,
        (ProEtale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).mapIso
            (theta T r hA a) ≪≫ e a =
          (ProEtale.comparisonUpperStarCompUpperStarIso
            (ModuleCat.{u + 1} (bottomCoefficient P)) v).app (bottomEtaleTwist P T r hA a) ≪≫
              (bottomNu P T').mapIso (c a) ≪≫ theta T' r hA a)

/-- The normalized etale coefficient restriction, on the underlying abelian sheaves.
It uses the actual root/evaluation-normalized pullback data stored in Theta.
Source: Stacks 03PK, finite-twist pullback (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomLocalCoefficientEt {P : PurityFiniteSetting.{u}} (Theta : SignedFiniteTateComparison P)
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))] (U : X.Etale)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ) :
    (Etale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance).obj
      ((bottomForgetEt (bottomCoefficient P) X).obj (bottomEtaleTwist P X r hA a)) ≅
    (bottomForgetEt (bottomCoefficient P) U.left).obj (bottomEtaleTwist P U.left r hA a) :=
  letI : U.left.Over (Spec (CommRingCat.of P.field.k)) :=
    ⟨U.hom ≫ (X ↘ Spec (CommRingCat.of P.field.k))⟩
  (bottomForgetEt (bottomCoefficient P) U.left).mapIso
    (((Etale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} (bottomCoefficient P)) U.hom inferInstance).app
        (bottomEtaleTwist P X r hA a)).symm ≪≫
      (Theta.pullback X U.left U.hom r hA).1 a)

/-- The scalar-forgotten comparison adjunct. This is the specified coefficient unit,
followed by the coefficient identification, rather than an arbitrary quasi-isomorphism.
Source: Stacks 099V (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomCoefficientUnit (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ)
    (theta : (bottomNu P X).obj (bottomEtaleTwist P X r hA a) ≅ bottomProLine P X a) :=
  (bottomForgetEt (bottomCoefficient P) X).map
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (bottomCoefficient P)) X).unit.app
      (bottomEtaleTwist P X r hA a) ≫
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (bottomCoefficient P)) X).map theta.hom)

/-- The inclusion of a section kernel into ordinary sections.
Source: Stacks 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomSupportInclusion {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    {V W : C} (j : W ⟶ V) :
    Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} j ⟶
      sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙ (evaluation _ _).obj (op V) where
  app F := kernel.ι (F.obj.map j.op)
  naturality f := by simp [Sheaf.supportedSectionsFunctor]

/-- The literal final-object evaluation after etale localization.
Source: Stacks 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomRestrictionEvaluationEt {X : Scheme.{u}} (U : X.Etale) :
    Etale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance ⋙
      bottomEvalEt (Scheme.Etale.mk (𝟙 U.left)) ≅ bottomEvalEt U :=
  NatIso.ofComponents
    (fun F ↦ F.obj.mapIso
      ((MorphismProperty.Over.isoMk (Iso.refl _)
        (by change 𝟙 _ ≫ (𝟙 _ ≫ U.hom) = U.hom; simp only [Category.id_comp]) :
        U ≅ (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.hom)).obj
          (Scheme.Etale.mk (𝟙 U.left)))).op)
    (by intro F G f; exact (f.hom.naturality _).symm)

/-- The literal final-object evaluation after pro-etale localization.
Source: Stacks 099R (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomRestrictionEvaluationPro {X : Scheme.{u}} (U : X.Etale) :
    ProEtale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance ⋙
      bottomEvalPro (Scheme.Etale.mk (𝟙 U.left)) ≅ bottomEvalPro U :=
  NatIso.ofComponents
    (fun F ↦ F.obj.mapIso
      ((MorphismProperty.Over.isoMk (Iso.refl _)
        (by change 𝟙 _ ≫ (𝟙 _ ≫ U.hom) = U.hom; simp only [Category.id_comp]) :
        (Scheme.toProEt X).obj U ≅
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale U.hom)).obj
            (Scheme.ProEt.mk (𝟙 U.left)))).op)
    (by intro F G f; exact (f.hom.naturality _).symm)

/-- A localized injective resolution and the actual kernel identity on its evaluated terms.
All identifications are conclusions of the theorem. The augmentation and kernel-inclusion
identities exclude arbitrary changes of the supported classes.
Source: Stacks 09XP and 09XQ (blueprint: lem-pur-supported-bottom-gluing). -/
structure SupportedLocalResolution
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (F : C) (I : InjectiveResolution F) (Q : C ⥤ C) [Q.Additive]
    (R : C ⥤ D) [R.Additive] (S : D ⥤ AddCommGrpCat.{u + 1}) [S.Additive]
    (E : C ⥤ AddCommGrpCat.{u + 1}) [E.Additive]
    (G : D ⥤ AddCommGrpCat.{u + 1})
    (alpha : Q ⋙ E ⟶ E) (beta : S ⟶ G) (epsilon : R ⋙ G ≅ E) where
  resolution : InjectiveResolution (R.obj F)
  restriction : resolution.cocomplex ≅ (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex
  augmentation : resolution.ι.f 0 ≫ restriction.hom.f 0 = R.map (I.ι.f 0)
  kernel : (S.mapHomologicalComplex (ComplexShape.up ℕ)).obj resolution.cocomplex ≅
    (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  kernel_sections : ∀ n : ℕ, kernel.hom.f n ≫ alpha.app (I.cocomplex.X n) =
    beta.app (resolution.cocomplex.X n) ≫ G.map (restriction.hom.f n) ≫
      epsilon.hom.app (I.cocomplex.X n)

/-- The common injective model fixes the supported comparison by the comparison adjunct
and by the identity on support kernels. This is the resolution normalization of the
composite `RΓ_Z(η)` followed by the direct-image comparison and the signed coefficient map.
Source: Stacks 099V, 09XP; normalization in lem-pur-derived-support-comparison-direct-image
(blueprint: lem-pur-supported-bottom-gluing). -/
structure SupportedBottomModel (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ)
    (Theta : SignedFiniteTateComparison P) where
  [additiveEt : (Etale.supportedKernel i.openComplement.ι).Additive]
  [additivePro : (bottomProKernel i).Additive]
  I : InjectiveResolution
    ((bottomForgetEt (bottomCoefficient P) X).obj (bottomEtaleTwist P X r hA a))
  J : InjectiveResolution
    ((bottomForgetPro (bottomCoefficient P) X).obj (bottomProLine P X a))
  resolution :
    ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex ≅ I.cocomplex
  unit_normalization : bottomCoefficientUnit P X r hA a (Theta.theta X r hA a) ≫
    (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).map (J.ι.f 0) ≫
      resolution.hom.f 0 = I.ι.f 0
  kernelIdentity : bottomProKernel i ⋙ ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X ≅
    ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X ⋙
      Etale.supportedKernel i.openComplement.ι
  kernel_normalization : ∀ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1},
    (kernelIdentity.hom.app F) ≫
      (kernel.ι (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        i.openComplement.ι).unit).app
          ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).obj F) =
    (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).map
      ((kernel.ι (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        i.openComplement.ι).unit).app F)
  localEt : ∀ U : X.Etale,
    SupportedLocalResolution _ I (Etale.supportedKernel i.openComplement.ι)
      (Etale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance)
      (Etale.supportSections (pullback.snd i U.hom)) (bottomEvalEt U)
      (bottomEvalEt (Scheme.Etale.mk (𝟙 U.left)))
      (Functor.whiskerRight
        (kernel.ι (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          i.openComplement.ι).unit) (bottomEvalEt U))
      (bottomSupportInclusion _ (Etale.supportRestrictionArrow (pullback.snd i U.hom)))
      (bottomRestrictionEvaluationEt U)
  localPro : ∀ U : X.Etale,
    SupportedLocalResolution _ J (bottomProKernel i)
      (ProEtale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance)
      (Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology U.left) AddCommGrpCat.{u + 1}
        (ProEtale.supportRestrictionArrow (pullback.snd i U.hom))) (bottomEvalPro U)
      (bottomEvalPro (Scheme.Etale.mk (𝟙 U.left)))
      (Functor.whiskerRight
        (kernel.ι (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          i.openComplement.ι).unit) (bottomEvalPro U))
      (bottomSupportInclusion _ (ProEtale.supportRestrictionArrow (pullback.snd i U.hom)))
      (bottomRestrictionEvaluationPro U)

namespace SupportedBottomModel

/-- The actual sheaf-support complex of the etale injective resolution.
Its homology is the recorded derived cohomology sheaf, equivalently R^q P(F).
Source: Stacks 015N and 09XQ (blueprint: lem-pur-supported-bottom-gluing). -/
def etaleComplex {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta) :=
  letI := M.additiveEt
  ((Etale.supportedKernel i.openComplement.ι).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj M.I.cocomplex

/-- The identical pro-etale sheaf-support complex, on its injective resolution.
Source: Stacks 09XP and 099R (blueprint: lem-pur-supported-bottom-gluing). -/
def proComplex {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta) :=
  letI := M.additivePro
  ((bottomProKernel i).mapHomologicalComplex (ComplexShape.up ℕ)).obj M.J.cocomplex

/-- The identity of support kernels in the common injective model.
The augmentation equation in M fixes the comparison adjunction unit; the kernel equation
fixes the direct-image comparison b. Hence the inverse of this identity is exactly the
canonical supported comparison specified in the node, including the signed theta.
Source: Stacks 099V; lem-pur-derived-support-comparison-direct-image, kernel normalization
(blueprint: lem-pur-supported-bottom-gluing). -/
def supportComplexIso {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta) :
    ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj M.proComplex ≅ M.etaleComplex :=
  letI := M.additiveEt
  letI := M.additivePro
  (NatIso.mapHomologicalComplex M.kernelIdentity (ComplexShape.up ℕ)).app M.J.cocomplex ≪≫
    ((Etale.supportedKernel i.openComplement.ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapIso M.resolution

/-- The canonical supported comparison on every etale object, with its restriction maps.
It is the inverse of the normalized identity on injective support complexes above.
Source: Stacks 099V and 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def comparison {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta)
    (d : ℕ) : bottomComplexPresheaf M.etaleComplex d ≅
      bottomProComplexPresheaf M.proComplex d :=
  (Functor.isoWhiskerRight
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso
      (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).mapIso M.supportComplexIso))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1}
      (ComplexShape.up ℕ) d)).symm

end SupportedBottomModel

end AlgebraicGeometry
