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
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
import Mathlib.CategoryTheory.Sites.LocallyBijective
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
public import Submission.WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicActualNormalization

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Etale presentations and scalar transport for a supplied algebraic tower

Source: Stacks Project, Tags 09C6, 09BV and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The lifted finite quotient ring at a level.
Source: Stacks Tag 09C6, with coefficient universes made explicit.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
abbrev finitePerfectAdicIsomorphismRing {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))

/-- Consecutive quotient homomorphism in the lifted coefficient universe.
Source: Stacks Tag 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
def finitePerfectAdicIsomorphismQuotient {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    finitePerfectAdicIsomorphismRing d (n + 1) →+* finitePerfectAdicIsomorphismRing d n :=
  (ULift.ringEquiv : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) ≃+*
    (A ⧸ d.ideal ^ (n + 1))).symm.toRingHom.comp
    ((Ideal.Quotient.factorPowSucc d.ideal (n + 1)).comp
      (ULift.ringEquiv : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)) ≃+*
        (A ⧸ d.ideal ^ (n + 1 + 1))).toRingHom)

/-- A finite-coefficient etale complex on a chart.
Source: Stacks Tags 09AL and 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
abbrev finitePerfectAdicIsomorphismComplex {A : Type t} [CommRing A]
    (Y : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :=
  DerivedCategory (Sheaf Y.smallEtaleTopology
    (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n)))

/-- Etale finite-level data before sheafification and section evaluation.

The presheaf maps have their normalization equation only on etale generators.
The scalar-forgetting realization functors, coefficient interchange and two level
comparisons have their actual normalization identities. Transport of raw isomorphisms
and preservation of a supplied raw square are then constructed and proved below. Neither
evaluation on pro-etale sheaf sections nor its reduction square is contained in the datum.
Source: Stacks Tags 09C6, 09BV and 06YY.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
structure FinitePerfectAdicIsomorphismPresentation
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d) where
  C : ∀ n : ℕ, finitePerfectAdicIsomorphismComplex V.left d n
  K : ∀ n : ℕ, finitePerfectAdicIsomorphismComplex V.left d n
  boundedC : ∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) i).obj (C n))
  lisseC : ∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) i).obj (C n))
  boundedK : ∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) i).obj (K n))
  lisseK : ∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) i).obj (K n))
  stalk : ∀ (n : ℕ) (Ω : Type t) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ V.left), Nonempty
      ((pointSmallEtale x).sheafFiber.obj (derivedLocalIsomorphismSheaf (C n) (K n)))
  dC : ∀ n : ℕ, C (n + 1) ⟶
    (normalizationRestrict V.left.smallEtaleTopology
      (finitePerfectAdicIsomorphismQuotient d n)).obj (C n)
  dK : ∀ n : ℕ, K (n + 1) ⟶
    (normalizationRestrict V.left.smallEtaleTopology
      (finitePerfectAdicIsomorphismQuotient d n)).obj (K n)
  p : ∀ n : ℕ, derivedLocalIsomorphismPresheaf (C (n + 1)) (K (n + 1)) ⟶
    derivedLocalIsomorphismPresheaf (C n) (K n)
  normalized : ∀ (n : ℕ) (U : V.left.Etale)
    (e : (localIsomorphismRestriction V.left
        (finitePerfectAdicIsomorphismRing d (n + 1)) U).obj (C (n + 1)) ≅
      (localIsomorphismRestriction V.left
        (finitePerfectAdicIsomorphismRing d (n + 1)) U).obj (K (n + 1))),
    e.hom ≫ etaleIsomorphismNormalizationArrow V.left
        (finitePerfectAdicIsomorphismQuotient d n) (dK n) U =
      etaleIsomorphismNormalizationArrow V.left
        (finitePerfectAdicIsomorphismQuotient d n) (dC n) U ≫
      (normalizationRestrict U.left.smallEtaleTopology
        (finitePerfectAdicIsomorphismQuotient d n)).map ((p n).app (op U) e).hom
  realization : ∀ (U : V.left.ProEt) (W : X.ProEt),
    (W ⟶ finitePerfectAdicChartObject V U) → ∀ n : ℕ,
    DerivedCategory (Sheaf (ProEt.topology U.left)
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) ⥤
      DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over W))
  scalar : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    normalizationRestrict (ProEt.topology U.left)
        (finitePerfectAdicIsomorphismQuotient d n) ⋙ realization U W f (n + 1) ≅
      realization U W f n
  actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (K n)) ≅
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
        (op n)
  model : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (C n)) ≅
      (finitePerfectAdicModelDiagram X d W T).obj (op n)
  actual_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (finitePerfectAdicIsomorphismQuotient d n) (dK n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (K n)) ≫
      (actual U W f n).hom =
    (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
        (homOfLE (Nat.le_succ n)).op
  model_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (finitePerfectAdicIsomorphismQuotient d n) (dC n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (C n)) ≫
      (model U W f n).hom =
    (model U W f (n + 1)).hom ≫
      (finitePerfectAdicModelDiagram X d W T).map (homOfLE (Nat.le_succ n)).op

/-- Apply the scalar-forgetting realization and the two specified level comparisons.
Source: Stacks Tag 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
def FinitePerfectAdicIsomorphismPresentation.transport
    {X : Scheme.{t}} {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    {M : DerivedCategory (CompletedAdicModules X d)} {V : X.Etale}
    {T : FinitePerfectAdicAlgebraTower d}
    (D : FinitePerfectAdicIsomorphismPresentation X d M V T)
    (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
    (e : (localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (D.C n) ≅
      (localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (D.K n)) :
    (finitePerfectAdicModelDiagram X d W T).obj (op n) ≅
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
        (op n) :=
  (D.model U W f n).symm ≪≫ (D.realization U W f n).mapIso e ≪≫ D.actual U W f n

end AlgebraicGeometry.Scheme
