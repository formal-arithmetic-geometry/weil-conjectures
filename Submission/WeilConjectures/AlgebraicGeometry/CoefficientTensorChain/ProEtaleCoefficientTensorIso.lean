/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientPullback
public import Submission.WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
public import Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Submission.WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
public import Mathlib.Algebra.Category.Ring.Limits
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Submission.WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
public import Submission.WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
public import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import Submission.WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import Submission.WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import Submission.WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
public import Submission.WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientTensorChain.ProEtaleCoefficientTensorIsoNaturality

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The normalized chain tensor isomorphism for coefficient restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The normalized chain tensor isomorphism supplied by ring-isomorphism transport.
(blueprint: def-pbc-coefficient-restriction-tensor-iso) -/
def tensorIso (o : SheafOfModules.RingIsoTensorTransport
    (J := ProEt.topology X)
    (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c) :
    total X S ⋙ (pbcRestrict c.hom).mapHomologicalComplex (.up ℤ) ≅
      (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).prod
        ((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ))) ⋙
        total X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  NatIso.ofComponents (fun Z ↦ o.totalIso Z.1 Z.2)
    (fun v ↦ tensorIso_naturality f R S c o _ _ v)

/-- The normalized tensor isomorphism has the prescribed map on every total summand.
Source: RingIsoTensorTransport.total_summand; Stacks Tag 07A4.
(blueprint: def-pbc-coefficient-restriction-tensor-iso)

Proof: the isomorphism is built from the supplied totalIso components. Substitute
that definition and apply the given summand normalization. This is an equation of
actual total complexes, including zero complexes and the identity coefficient map. -/
theorem tensorIso_summand
    (o : SheafOfModules.RingIsoTensorTransport (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (P Q : CochainComplex (proEtaleRingModules X S) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    (pbcRestrict c.hom).map
        (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor X S) a b n h) ≫
        ((tensorIso f R S c o).hom.app (P, Q)).f n =
      o.monoidal.toMonoidal.toOplaxMonoidal.δ (P.X a) (Q.X b) ≫
        CochainComplex.ιMapBifunctor
          (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).obj P)
          (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).obj Q)
          (proEtaleOrdinaryTensor X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
          a b n h := by
  simpa only [tensorIso, NatIso.ofComponents_hom_app] using o.total_summand P Q a b n h

end AlgebraicGeometry.Scheme.CoefficientTensorChain
