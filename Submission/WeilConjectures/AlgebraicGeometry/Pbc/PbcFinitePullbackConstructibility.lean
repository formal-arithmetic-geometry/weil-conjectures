/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-! # Constructible finite-coefficient module pullback
Source: preservation proof, step 5; Stacks Tags 09AI and 09AL
(blueprint: lem-weil-pbc-finite-pullback-constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.ProEtale

private def scalarRestriction (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  ConstantScalarComparison.restriction (ProEt.topology T) A
    (adicLisseRing T A) (adicLisseConstantUnit T A)

private abbrev scalarEmbedding (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    ProEtale.finiteCoefficientModulePresheaf T.ProEt A

private instance (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarEmbedding T A).Full := by
  unfold scalarEmbedding
  let := (ProEtale.coefficientModulePresheafFullyFaithful T.ProEt A).full
  infer_instance
private instance (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarEmbedding T A).Faithful := by
  unfold scalarEmbedding
  let := (ProEtale.coefficientModulePresheafFullyFaithful T.ProEt A).faithful
  infer_instance

private instance scalarRestriction_full (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarRestriction T A).Full :=
  (ConstantScalarComparison.restrictionFullyFaithful (ProEt.topology T) A
    (adicLisseRing T A) (adicLisseConstantUnit T A)).full
private instance scalarRestriction_faithful (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarRestriction T A).Faithful :=
  (ConstantScalarComparison.restrictionFullyFaithful (ProEt.topology T) A
    (adicLisseRing T A) (adicLisseConstantUnit T A)).faithful

private instance scalarRestriction_essSurj (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarRestriction T A).EssSurj where
  mem_essImage F := by
    let P := (scalarEmbedding T A).obj F
    let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (adicLisseConstantUnit T A)
    have hη : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify (ProEt.topology T) P.presheaf)
      exact isIso_toSheafify (ProEt.topology T)
        ((sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F).property
    refine ⟨(PresheafOfModules.sheafification.{u + 1}
      (adicLisseConstantUnit T A)).obj P, ⟨?_⟩⟩
    exact (Functor.FullyFaithful.ofFullyFaithful (scalarEmbedding T A)).preimageIso
      (asIso (adj.unit.app P)).symm

private instance scalarRestriction_equivalence (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] : (scalarRestriction T A).IsEquivalence := {}

@[irreducible] private def constantCoefficients {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (adicLisseConstantRing X A) ≅
      adicLisseConstantRing Y A := by
  letI : IsIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of A)) := proEtaleConstantComparison_isIso g (CommRingCat.of A)
  exact asIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1} (CommRingCat.of A))

private abbrev relativeRing {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :=
  (adicLisseForget Y).obj
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (adicLisseConstantRing X A))

private def relativeUnit {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A) ⟶ (relativeRing g A).obj :=
  adicLisseConstantUnit Y A ≫ ((adicLisseForget Y).map (constantCoefficients g A).inv).hom

private instance relativeUnit_surjective {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallySurjective (ProEt.topology Y) (relativeUnit g A) := by
  unfold relativeUnit
  infer_instance

private abbrev relativeRestriction {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :=
  ConstantScalarComparison.restriction (ProEt.topology Y) A
    (relativeRing g A) (relativeUnit g A)

@[irreducible] private def scalarConstant (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M : ModuleCat.{u + 1} A) :
    (scalarRestriction X A).obj ((adicLisseConstantModules X A).obj M) ≅
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M :=
  letI := ConstantScalarComparison.constantComparisonHom_isIso (ProEt.topology X) A
    (adicLisseRing X A) (adicLisseConstantUnit X A) M
  (asIso (ConstantScalarComparison.constantComparisonHom (ProEt.topology X) A
    (adicLisseRing X A) (adicLisseConstantUnit X A) M)).symm

end AlgebraicGeometry.Scheme
