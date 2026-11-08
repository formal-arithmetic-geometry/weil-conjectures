/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Noetherian

import all Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOrigin
import Submission.WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantSliceDerivedStalkComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.AB
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
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
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Submission.WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Topology.Connected.Clopen
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
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
import Submission.WeilConjectures.Mathlib.Topology.NoetherianSpace

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Connected etale presentations before choosing local stalk markings

Source: Stacks Project, proetale.tex, Tags 09AL, 09B1 and 09C6.
(blueprint: lem-weil-pbc-lisse-tower-connected-etale-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local irreducible] constantAdicQuotientRealization

/-- Etale origins and scalar-normalized stalk arrows on one connected chart.
The transport field only transports a supplied isomorphism; it asserts no local
markings or covering sieves of markings.

Source: Stacks Project, proetale.tex, Tags 09AL, 09B1 and 09C6, before local constancy.
(blueprint: lem-weil-pbc-lisse-tower-connected-etale-presentation). -/
structure LisseTowerConnectedEtalePresentation
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (V : Y.Etale) where
  connected : ConnectedSpace V.left
  point : V.left
  level : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
  bounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj (level n))
  lisse : ∀ (n : ℕ) (q : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj (level n))
  vanishing : ∀ (n : ℕ) (q : ℤ),
    IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)) →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj (level n))
  transition : ∀ n : ℕ,
    (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
      ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
        (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1))))
      (Functor.additive_of_preserves_binary_products _) _ _).obj (level (n + 1)) ⟶
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := d.ideal.map
          (algebraMap A (AdicCompletion d.ideal A))) (Nat.le_succ (n + 1))))).mapDerivedCategory.obj
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
            (AdicCompletion d.ideal A ⧸
              (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
          (Functor.additive_of_preserves_binary_products _) _ _).obj (level n))
  universal : ∀ (n : ℕ)
    (N : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))),
    Function.Bijective (fun k :
      (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
          (AdicCompletion d.ideal A ⧸
            (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
        (Functor.additive_of_preserves_binary_products _) _ _).obj (level n) ⟶ N ↦
          transition n ≫
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
              (Ideal.pow_le_pow_right (I := d.ideal.map
                (algebraMap A (AdicCompletion d.ideal A)))
                (Nat.le_succ (n + 1))))).mapDerivedCategory.map k)
  refinementLisse : ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj V) (n : ℕ) (q : ℤ),
    IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj (M.level n))))
  transport : ∀ (n : ℕ) (Z : V.left.Etale),
    Nonempty ((AlgebraicGeometry.Etale.upperStar _ Z.hom).mapDerivedCategory.obj (level n) ≅
      (constantSheaf Z.left.smallEtaleTopology _).mapDerivedCategory.obj
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
            (AdicCompletion d.ideal A ⧸
              (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
          (Functor.additive_of_preserves_binary_products _) _ _).obj (level n))) →
    ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj (Etale.mk (Z.hom ≫ V.hom))),
      Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj
        ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          ((V.left.uliftPointSmallEtale point).sheafFiber (A := ModuleCat.{u + 1}
            (AdicCompletion d.ideal A ⧸
              (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
          (Functor.additive_of_preserves_binary_products _) _ _).obj (level n)) ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj (M.level n))

end AlgebraicGeometry.Scheme
