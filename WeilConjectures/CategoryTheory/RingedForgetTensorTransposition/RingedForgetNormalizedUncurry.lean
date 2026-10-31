/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorDescent
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetRepresentativeEvaluation
import all WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationCoherence
import all WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationTranspose
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Normalized uncurrying under exact ringed forgetting

Source: Stacks 08J9, 070I; steps 5--8 of ringed tensor transposition
(blueprint: lem-sf-ringed-forget-normalized-uncurry).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe b vb a va c v r d vd s wb wa

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory.RingedForgetTensorTransposition

-- Reuse the small-site transport directly when elaborating coefficient-ring compositions.
attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective


variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

variable (χ : RingedForgetTwoInjective.Comparison.{wb, wa, c, v, r, d, vd, s}
    J R J' R' U u.hom)

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolution coefficientHomResolutionIso coefficientHomResolutionInverse
  coefficientTotalTensor coefficientTensorGenerator CoefficientTensorModels.iso


omit [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U] in
private theorem evaluation_compatibility
    (m : TensorComparison.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA)
    (preserves_flat_models :
      ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
        P.IsKFlatIndependentCoefficients →
        (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) (P.X p)) →
        CochainComplex.IsKFlatIndependentCoefficients (R := R')
          ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
          (R := R') (U.obj (P.X p)))
    (K L : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    m.derived.inv.app ((derivedInternalHomOfUniverses.{c, v, r, wb} J R).obj (op K, L), K) ≫
        U.mapDerivedCategory.map (SB.evaluation K L) =
      SA.tensor.map
        (X := (U.mapDerivedCategory.obj
          ((derivedInternalHomOfUniverses.{c, v, r, wb} J R).obj (op K, L)),
          U.mapDerivedCategory.obj K))
        (Y := ((derivedInternalHomOfUniverses.{d, vd, s, wa} J' R').obj
          (op (U.mapDerivedCategory.obj K), U.mapDerivedCategory.obj L),
          U.mapDerivedCategory.obj K))
        (χ.derived.hom.app (op K, L), 𝟙 _) ≫
        SA.evaluation (U.mapDerivedCategory.obj K) (U.mapDerivedCategory.obj L) := by
  let X := DerivedCategory.Q.objPreimage K
  obtain ⟨P, f, hP, fP, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  obtain ⟨I, _, ⟨e'⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective L
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  apply evaluation_of_iso (comparisonData J R J' R' U u SB TB βB cB SA TA βA cA χ m) e e'.symm
  apply ringed_forget_representative_evaluation J R J' R' U u SB TB βB cB SA TA βA cA χ m
    preserves_flat_models P I hP
  intro n
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (fP n)

-- Preserve the original public product-preservation binder, unused by the shorter proof.
set_option linter.unusedSectionVars false in
/-- The fixed two-injective Hom comparison preserves normalized uncurrying for the
specified tensor comparison and the flat-model preservation hypothesis.
No double-dual or coherence conclusion is asserted.

Source: Stacks 08J9, 070I; steps 5--8 of
lem-sf-ringed-forget-tensor-transposition
(blueprint: lem-sf-ringed-forget-normalized-uncurry).

Proof: represent M,K by flat-term K-flat P,S and L by V with its fixed K-injective
augmentation V to I. The assumed preservation makes UP and US K-flat, so the
tensor representative square applies to this pair. The Hom complex Hom(S,I) is
K-injective; localization bijectivity
represents the given derived arrow by a chain map phi from P to Hom(S,I).
The fixed adjunction uncurries phi by psi(x tensor y)=phi(x)(y), followed by the
inverse localized augmentation. On each Hom projection and each tensor summand,
the specified underived evaluation square says that U psi agrees with evaluation
of the product-Hom comparison applied to U phi, composed with the tensor comparison.
Choose the homotopy comparison j from UI to the target fixed replacement I' of UV.
Its composite with U eta is homotopic to eta', by K-injective localization bijectivity.
The two-injective comparison is natural under source replacement and target j, so
the target normalized uncurry is represented by j U psi c inverse followed by
q(eta') inverse. The equality q(eta') inverse q(j)=q(U eta) inverse and the tensor
representative equation give the displayed formula. Localization injectivity removes
choices of lifts; K-flat resolutions cover every source object. -/
theorem ringed_forget_normalized_uncurry
    (m : TensorComparison.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA)
    (_preserves_flat_models :
      ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
        P.IsKFlatIndependentCoefficients →
        (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) (P.X p)) →
        CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
          ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
            (R := R') (U.obj (P.X p)))
    (M K L : DerivedCategory (RingedTensorModules.{c, v, r} J R))
    (f : M ⟶ (derivedInternalHomOfUniverses.{c, v, r, wb} J R).obj (op K, L)) :
    (SA.transpose (U.mapDerivedCategory.obj M) (U.mapDerivedCategory.obj K)
        (U.mapDerivedCategory.obj L)).symm
        (U.mapDerivedCategory.map f ≫ χ.derived.hom.app (op K, L)) =
      m.derived.inv.app (M, K) ≫
        U.mapDerivedCategory.map ((SB.transpose M K L).symm f) := by
  have he := evaluation_compatibility J R J' R' U u SB TB βB cB SA TA βA cA χ m
    _preserves_flat_models K L
  have ht := transpose_of_evaluation
    (comparisonData J R J' R' U u SB TB βB cB SA TA βA cA χ m) K L he M
    ((SB.transpose M K L).symm f)
  apply (SA.transpose _ _ _).injective
  rw [Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply, comparisonData, makeComparisonData,
    Iso.app_hom, Iso.app_inv] using ht.symm

end CategoryTheory.RingedForgetTensorTransposition
