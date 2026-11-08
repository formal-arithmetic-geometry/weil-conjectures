/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleStalkData
import Submission.WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Submission.WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Submission.WeilConjectures.CategoryTheory.LocalModuleHom
import Submission.WeilConjectures.CategoryTheory.LocalModuleIso
import Submission.WeilConjectures.CategoryTheory.ConstantLocalModuleHom
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleUnit
import Mathlib.Algebra.Module.FinitePresentation
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import Submission.WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Submission.WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import Submission.WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import Submission.WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import Submission.WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import Submission.WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.LinearAlgebra.StdBasis
import Submission.WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Finiteness.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Submission.WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.RingTheory.FiniteConeFreeModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.Algebra.Homology.Homotopy
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeEtaleAcyclicHomotopy
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Submission.WeilConjectures.RingTheory.RingPseudoCoherent
import Submission.WeilConjectures.RingTheory.FiniteFreeResolution
import Submission.WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.Single
import Submission.WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Submission.WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import Submission.WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import Submission.WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.LinearAlgebra.Dimension.Free
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Submission.WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicIsomorphismPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.SequentialLimit
import Mathlib.CategoryTheory.CofilteredSystem
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The ordinary limit of the actual coefficient module tower

Source: Stacks Project, Tag 09C6, the coefficient case of the finite-projective calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The actual finite-coefficient module diagram, including its specified transitions.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit). -/
def finitePerfectAdicCoefficientDiagram (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) : ℕᵒᵖ ⥤ CompletedAdicModules X d :=
  Functor.ofOpSequence (completedAdicFiniteModuleStep X d)

private theorem coefficientStep_apply (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : (completedAdicFiniteRing X d (n + 1)).obj.obj U) :
    (completedAdicFiniteModuleStep X d n).val.app U x =
      (completedAdicFiniteStep X d n).hom.app U x :=
  (completedAdicFiniteModuleStep_exists X d n).exists.choose_spec U x

/-- The limit projections, viewed as linear maps of coefficient modules.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit). -/
def finitePerfectAdicCoefficientProjection (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    SheafOfModules.unit (completedAdicRing X d) ⟶ completedAdicFiniteModule X d n where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (SheafOfModules.unit (completedAdicRing X d)).val.obj U)
        (Y := (completedAdicFiniteModule X d n).val.obj U)
        { toFun := (completedAdicProjection X d n).hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r x
            change (completedAdicRing X d).obj.obj U at x
            change (completedAdicProjection X d n).hom.app U (r * x) =
              (completedAdicProjection X d n).hom.app U r *
                (completedAdicProjection X d n).hom.app U x
            exact map_mul _ _ _ }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom
          ((completedAdicProjection X d n).hom.naturality f) x }

/-- The completed coefficient unit supplies a cone of actual quotient projections.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit). -/
def finitePerfectAdicCoefficientCone (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) : Cone (finitePerfectAdicCoefficientDiagram X d) where
  pt := SheafOfModules.unit (completedAdicRing X d)
  π := NatTrans.ofOpSequence (finitePerfectAdicCoefficientProjection X d) (by
    intro n
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (completedAdicRing X d).obj.obj U at x
    simp only [Functor.const_obj_map,
      finitePerfectAdicCoefficientDiagram, Functor.ofOpSequence_map_homOfLE_succ]
    change (completedAdicProjection X d n).hom.app U x =
      (completedAdicFiniteModuleStep X d n).val.app U
        ((completedAdicProjection X d (n + 1)).hom.app U x)
    rw [coefficientStep_apply]
    have h : completedAdicProjection X d (n + 1) ≫
        completedAdicFiniteStep X d n = completedAdicProjection X d n := by
      simpa only [completedAdicProjection, completedAdicRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using
        limit.w (completedAdicRingSystem X d) (homOfLE n.le_succ).op
    exact (congrArg (fun f : completedAdicRing X d ⟶
      completedAdicFiniteRing X d n ↦ (f.hom.app U).hom x) h).symm)

/-- A compatible finite-free retract of one degree of a coefficient tower and its cone.
The two cone equations retain the actual coefficient projections.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit). -/
structure FinitePerfectAdicCoefficientRetract (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (B : ℕᵒᵖ ⥤ CompletedAdicModules X d) (c : Cone B) where
  rank : ℕ
  inclusion : B ⟶ finitePerfectAdicCoefficientDiagram X d ⋙
    Functor.const (Discrete (Fin rank)) ⋙ lim
  projection : finitePerfectAdicCoefficientDiagram X d ⋙
    Functor.const (Discrete (Fin rank)) ⋙ lim ⟶ B
  splitting : inclusion ≫ projection = 𝟙 B
  coneInclusion : c.pt ⟶ (lim (J := Discrete (Fin rank))).obj
    ((Functor.const (Discrete (Fin rank))).obj (SheafOfModules.unit (completedAdicRing X d)))
  coneProjection : (lim (J := Discrete (Fin rank))).obj
    ((Functor.const (Discrete (Fin rank))).obj (SheafOfModules.unit (completedAdicRing X d)))
      ⟶ c.pt
  coneSplitting : coneInclusion ≫ coneProjection = 𝟙 c.pt
  inclusion_naturality : ∀ n : ℕᵒᵖ, coneInclusion ≫
    (Functor.const (Discrete (Fin rank)) ⋙ lim).map
      ((finitePerfectAdicCoefficientCone X d).π.app n) = c.π.app n ≫ inclusion.app n
  projection_naturality : ∀ n : ℕᵒᵖ, coneProjection ≫ c.π.app n =
    (Functor.const (Discrete (Fin rank)) ⋙ lim).map
      ((finitePerfectAdicCoefficientCone X d).π.app n) ≫ projection.app n

end AlgebraicGeometry.Scheme
