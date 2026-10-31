/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CofinalFiniteReductionConstructibility

import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # Integral reduction bounds from ell-power scalar extensions

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower,
final integral-constructibility sentence.
(blueprint: lem-sp-cofinal-integral-reduction-bounds)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
attribute [local instance high] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale

attribute [-instance] spCoefficientModulesAbelian
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

open SheafOfModules.SuccessiveDerivedQuotient

private noncomputable def cofinalPresentationIso
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
      (a : R ⟶ S), spCofinalScalarPresentation T a)
    (n : Normalization.{u + 1, u, u + 1, u + 2}
      (C := T.ProEt) (J := Scheme.ProEt.topology T)
      (hD := fun R ↦ HasDerivedCategory.standard (Modules.{u + 1, u, u + 1} R)) p)
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    n.right (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) a ≅
        @Functor.mapDerivedCategory (Modules.{u + 1, u, u + 1} S) _ _
          (HasDerivedCategory.standard _) (Modules.{u + 1, u, u + 1} R) _ _
          (HasDerivedCategory.standard _) (restriction.{u + 1, u, u + 1} a) _ _ _ := by
  let Q := @DerivedCategory.Qh (Modules.{u + 1, u, u + 1} S) _ _ (HasDerivedCategory.standard _)
  let W := HomotopyCategory.quasiIso (Modules.{u + 1, u, u + 1} S) (.up ℤ)
  let F := (restriction.{u + 1, u, u + 1} a).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let : Localization.Lifting Q W F
      (n.right (hD := fun R ↦ HasDerivedCategory.standard
        (Modules.{u + 1, u, u + 1} R)) a) :=
    ⟨n.right_factors (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) a⟩
  let : Localization.Lifting Q W F (restriction.{u + 1, u, u + 1} a).mapDerivedCategory :=
    ⟨(restriction.{u + 1, u, u + 1} a).mapDerivedCategoryFactorsh⟩
  exact Localization.liftNatIso Q W F F
    (n.right (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) a)
    (restriction.{u + 1, u, u + 1} a).mapDerivedCategory (Iso.refl F)

private theorem cofinalTor_of_iso (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro Q P hQ f hf hP N i hi
  obtain ⟨eQ⟩ := hQ
  exact h.2 Q P ⟨eQ ≪≫ e.symm⟩ f hf hP N i hi

/-- Uniformizer reductions of a completed object inherit constructibility and the
common Tor interval from all its ell-power reductions. This is independent of any
coefficient tower or chosen Roos presentation.
Source: current blueprint, sk-lem-sp-tower.proof.md, final integral-category sentence;
lem-sp-cofinal-finite-reduction-constructibility
(blueprint: lem-sp-cofinal-integral-reduction-bounds).

Proof: factor ell = v*pi^e with e>=1 by the coefficient-fiber lemma. For every j
choose N=j, so j+1 <= e*(N+1). The canonical cofinal quotient B_N -> O/pi^(j+1)
composed with spCompletedEllCommProjection is the uniformizer projection, by the
normalization of the completed coefficient comparison. Present D.scalar and
scalarReductionDerivedExtension by their universal left-derived scalar-extension
counits. The successive-quotient normalization compares their composite with the
derived uniformizer reduction; its equation on flat-term K-flat representatives
makes the comparison independent of presentations. Apply the cofinal finite
reduction constructibility theorem with these normalized presentations. Scalar
extension between the finite quotients preserves constructibility and the stated
Tor interval, without assuming that the quotient map is flat. Test that interval
on the unit module in degree zero to get the displayed cohomological vanishing.
Transport through the normalized comparison to the recorded uniformizer functor.
Neither completeness nor boundedness of the original M is assumed. -/
theorem sp_cofinal_integral_reduction_bounds
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (a b : ℤ) (hab : a ≤ b)
    (hM : ∀ n : ℕ,
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
        ((DerivedCategory.homologyFunctor _ i).obj
          ((D.scalar (spCompletedEllCommProjection l E T n)).model.T.obj M))) ∧
      Scheme.HasProEtaleTorAmplitude T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
        ((D.scalar (spCompletedEllCommProjection l E T n)).model.T.obj M) a b) :
    ∀ j : ℕ,
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
        (Padic.coefficientExtensionRing l E (j + 1))
        ((DerivedCategory.homologyFunctor _ i).obj
          ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T j).obj M))) ∧
      ∀ i : ℤ, i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor _ i).obj
          ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T j).obj M)) := by
  classical
  obtain ⟨e, v, he, hfactor⟩ := (sp_completed_coefficients_regular l E T).1
  obtain ⟨p, ⟨n⟩⟩ := successive_derived_quotient_normalization
    (J := Scheme.ProEt.topology T)
    (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R))
  have hi {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
      (p a).derived ≅ (D.scalar a).model.T :=
    ((n.adjunction (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) a).ofNatIsoRight
        (cofinalPresentationIso T p n a)).leftAdjointUniq (D.scalar a).adjunction
  have hp (N : ℕ) :
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (spCompletedEllCommProjection l E T N) =
        (sp_completed_coefficient_limit l E T).exists.choose.hom ≫
          limit.π (spCoefficientRings l E T) (op N) := by
    exact Functor.map_preimage _ _
  have h := (sp_cofinal_finite_reduction_constructibility l E T e he v hfactor
    (spCompletedEllCommProjection l E T) hp p n).2.2 M a b hab
  have hell (N : ℕ) := (hi (spCompletedEllCommProjection l E T N)).app M
  have hinput := h (fun N ↦ ⟨fun i ↦
    Scheme.constructibleProEtale_of_iso T _
      ((DerivedCategory.homologyFunctor _ i).mapIso (hell N).symm) ((hM N).1 i),
    cofinalTor_of_iso T _ (hell N).symm (hM N).2⟩)
  intro j
  let adj := (WeilConjectures.derivedScalarExtensionRestrictionAdjunction l E T j).choose
  let e' : (p (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T j)).derived ≅
      WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T j :=
    ((n.adjunction (hD := fun R ↦ HasDerivedCategory.standard
      (Modules.{u + 1, u, u + 1} R)) _).ofNatIsoRight
        (cofinalPresentationIso T p n _)).leftAdjointUniq adj
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_⟩
  · exact Scheme.constructibleProEtale_of_iso T _
      ((DerivedCategory.homologyFunctor _ i).mapIso (e'.app M)) ((hinput j).1 i)
  · exact ((hinput j).2.2 i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (e'.app M)).symm

end AlgebraicGeometry.ProEtale
