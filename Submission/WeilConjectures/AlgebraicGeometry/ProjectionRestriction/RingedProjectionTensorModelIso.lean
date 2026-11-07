/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import Submission.WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Submission.WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Normalized comparison with the published derived tensor

Source: Stacks Project, Tag 06YU (definition-derived-tor).
(blueprint: lem-weil-pbc-ringed-projection-tensor-model-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  HomologicalComplex₂.total MorphismProperty.Q'
  SheafOfModules.KFlatFixedTensor.representativeIso

private theorem publishedRepresentative (P Q : CochainComplex (Mod R) ℤ)
    (hp : resolving R P) (hq : resolving R Q) :
    SheafOfModules.cochainTensorRepresentativeArrow J R (⟨P, hp⟩, ⟨Q, hq⟩) =
      (SheafOfModules.KFlatFixedTensor.representativeIso R P Q hp.1 hq.1 hp.2 hq.2).hom := by
  unfold SheafOfModules.cochainTensorRepresentativeArrow
    SheafOfModules.KFlatFixedTensor.representativeIso
  simp only [id_eq, SheafOfModules.KFlatFixedTensor.TensorPresentation.representativeIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.prod_hom, Category.assoc]
  rfl

set_option maxHeartbeats 800000 in
-- Compare the two normalized representative interfaces without unfolding their tensor data.
/-- A tensor model is naturally identified with the published derived tensor, with
its specified representative comparison.
Source: Stacks Project, Tag 06YU (definition-derived-tor and its independence construction).
(blueprint: lem-weil-pbc-ringed-projection-tensor-model-iso).

Proof: apply cochain tensor model rigidity to the natural comparison of a. It
extends the comparison from resolving pairs to an isomorphism e of bifunctors.
The cochain representative arrow is the published representativeIso: the
quotient-to-derived factorization has identity components, so its initial
identity and the tensor's image of the product identity cancel. Evaluating the
normalization equation of rigidity at each resolving pair gives the displayed
equation. Both directions of e are supplied by the existing rigidity theorem;
there is no choice of a new tensor operation. The argument uses neither a bound
nor any shift or pullback hypotheses. -/
theorem ringedProjectionTensorModelIso (a : TensorModel R) :
    ∃ e : SheafOfModules.siteDerivedTensorIndependentCoefficients J R ≅ a.functor,
      ∀ (P Q : CochainComplex (Mod R) ℤ) (hp : resolving R P) (hq : resolving R Q),
        (SheafOfModules.KFlatFixedTensor.representativeIso R P Q hp.1 hq.1 hp.2 hq.2).hom ≫
          e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
            a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) := by
  obtain ⟨r, hr, he, _⟩ :=
    SheafOfModules.cochain_tensor_model_rigidity.{u + 1, u, u + 1, u + 2, 0, 0} J R
  obtain ⟨e, he, _⟩ := he a.functor a.representative
  refine ⟨e, ?_⟩
  intro P Q hp hq
  have h := congr_app he (⟨P, hp⟩, ⟨Q, hq⟩)
  change r.hom.app _ ≫ e.hom.app _ = _ at h
  rw [hr, publishedRepresentative P Q hp hq] at h
  exact h

end AlgebraicGeometry.Scheme.ProjectionRestriction
