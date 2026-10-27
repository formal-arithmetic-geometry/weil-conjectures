/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Sheaf.Paper.FlatRingedIdealCompleteEquivalence
public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Sheaf.Paper.ConstantCompletionKoszulReflector
public import Sheaf.Paper.ConstantCompletionInverseImage
import all Sheaf.Paper.ConstantCompletionInverseImage
public import Sheaf.CategoryTheory.FlatScalarKoszulModels
import all Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison
import all Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization
import all Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent
import Sheaf.CategoryTheory.CochainUniversalCounitTransport
import Sheaf.CategoryTheory.AugmentedDerivedTowerUnit
import all Sheaf.Paper.DerivedQuotientTowerPresentation
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Constant coefficient completion: Restriction

Restriction of the completions (`completion_restriction`) and of the Koszul comparison.

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe w

section D2Helpers
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory CochainComplex.IsAcyclicTensorKFlat
  CochainComplex.IsKFlatIndependentCoefficients
attribute [local irreducible] HasDerivedCategory.standard

namespace CategoryTheory.ConstantCompletion
private theorem transportCompletionUnit
    {B R : Type*} [Category B] [Category R]
    (F : B ⥤ R) (CB KB : B ⥤ B) (CR KR : R ⥤ R)
    (vB : 𝟭 B ⟶ CB) (vR : 𝟭 R ⟶ CR)
    (uB : ∀ M, M ⟶ KB.obj M) (uR : ∀ M, M ⟶ KR.obj M)
    (eR : KR ≅ CR) (eB : KB ≅ CB)
    (hR : ∀ N, uR N ≫ eR.hom.app N = vR.app N)
    (hB : ∀ M, uB M ≫ eB.hom.app M = vB.app M)
    (gamma : KB ⋙ F ≅ F ⋙ KR)
    (hg : ∀ M, F.map (uB M) ≫ gamma.hom.app M = uR (F.obj M)) :
    ∃ e : F ⋙ CR ≅ CB ⋙ F,
      ∀ M, vR.app (F.obj M) ≫ e.hom.app M = F.map (vB.app M) := by
  let e : F ⋙ CR ≅ CB ⋙ F := Functor.isoWhiskerLeft F eR.symm ≪≫
    gamma.symm ≪≫ Functor.isoWhiskerRight eB F
  refine ⟨e, ?_⟩
  intro M
  change vR.app (F.obj M) ≫
    (eR.inv.app (F.obj M) ≫ gamma.inv.app M ≫ F.map (eB.hom.app M)) = _
  rw [← hR, Category.assoc, eR.hom_inv_id_app_assoc]
  have hu : uR (F.obj M) ≫ gamma.inv.app M = F.map (uB M) := by
    rw [← hg M, Category.assoc, gamma.hom_inv_id_app]
    exact Category.comp_id _
  rw [← Category.assoc, hu, ← F.map_comp, hB]

end CategoryTheory.ConstantCompletion

namespace CategoryTheory.FlatScalarKoszul
variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}
variable [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules B)]
variable [HasDerivedCategory.{w} (Towers R)] [HasDerivedCategory.{w} (Towers B)]
private theorem arbitraryKoszulCompletion (φ : R ⟶ B)
    (hflat : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor φ) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor φ))
    (r : ℕ) (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (DB : RingedKoszulLimitPresentation B r (imageSections φ a))
    (DR : RingedKoszulLimitPresentation R r a) :
    ∃ gamma : DB.completion ⋙ restrictDerived φ ≅ restrictDerived φ ⋙ DR.completion,
      ∀ E, (restrictDerived φ).map (DB.unit E) ≫ gamma.hom.app E =
        DR.unit ((restrictDerived φ).obj E) := by
  obtain ⟨h, _, hu⟩ := strictScalarKoszulComparison φ r a
  obtain ⟨hD, hd⟩ := descendedTensorComparison φ r a DB DR h
  obtain ⟨alpha, ha⟩ := normalizedLimitComparison φ hflat r a DB DR
  let gamma : DB.completion ⋙ restrictDerived φ ≅ restrictDerived φ ⋙ DR.completion :=
    Functor.isoWhiskerLeft DB.tensorTower alpha ≪≫
      Functor.isoWhiskerRight hD DR.inverseLimit
  refine ⟨gamma, ?_⟩
  intro E
  apply unitCompatibility_of_Q φ r a DB DR gamma _ E
  intro N
  have hN := derivedUnitRestrictionOnComplex φ r a DB DR h hD hd alpha ha hu N
  dsimp only [gamma, RingedKoszulLimitPresentation.completion, Functor.comp_obj,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hN ⊢
  simpa only [Category.assoc] using hN
end CategoryTheory.FlatScalarKoszul

end D2Helpers

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation

private theorem chosenKoszulRestriction [IsNoetherianRing A]
    (r : ℕ) (a : Fin r → A)
    (KB : KoszulPresentation J A I true r a)
    (KR : KoszulPresentation J A I false r a) :
    ∃ gamma : koszulCompletion J A I KB ⋙ dres (coefficientMap J A I) ≅
        dres (coefficientMap J A I) ⋙ koszulCompletion J A I KR,
      ∀ M, (dres (coefficientMap J A I)).map (koszulUnit J A I KB M) ≫
        gamma.hom.app M = koszulUnit J A I KR ((dres (coefficientMap J A I)).obj M) := by
  let := HasDerivedCategory.standard (Mod (constant J A))
  let := HasDerivedCategory.standard (Mod (completed J A I))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (constant J A))
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (completed J A I))
  have hf := change_exact (coefficientMap J A I) (flat_and_quotients J A I).1
  exact FlatScalarKoszul.arbitraryKoszulCompletion
    (coefficientMap J A I) hf r
    (fun i ↦ algebraSection (baseMap J A I false) (a i)) KB KR

/-- Restriction identifies both completions and their specified units.
Source: Stacks 099L, 099M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: at the representative level finite reduction comparisons and dual Koszul tensor
comparisons preserve their strict transitions and degree-zero units. Restriction carries
K-injective strict tower resolutions to K-injective resolutions, since it is right
adjoint to flat exact extension of scalars. Apply limits and the universal comparisons.
This gives the natural isomorphism and the stated equality of the actual units. -/
theorem completion_restriction [IsNoetherianRing A] :
    ∃ e : dres (coefficientMap J A I) ⋙ completion J A I false ≅
        completion J A I true ⋙ dres (coefficientMap J A I),
      ∀ M : D (completed J A I),
        (completionUnit J A I false).app ((dres (coefficientMap J A I)).obj M) ≫
          e.hom.app M =
        (dres (coefficientMap J A I)).map ((completionUnit J A I true).app M) := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    I.fg_of_isNoetherianRing
  obtain ⟨KR, ⟨eR, heR⟩, _⟩ := koszul_quotient_reflector J A I false r a ha
  obtain ⟨KB, ⟨eB, heB⟩, _⟩ := koszul_quotient_reflector J A I true r a ha
  obtain ⟨gamma, hg⟩ := chosenKoszulRestriction J A I r a KB KR
  exact transportCompletionUnit (dres (coefficientMap J A I))
    (completion J A I true) (koszulCompletion J A I KB)
    (completion J A I false) (koszulCompletion J A I KR)
    (completionUnit J A I true) (completionUnit J A I false)
    (koszulUnit J A I KB) (koszulUnit J A I KR) eR eB heR heB gamma hg

set_option backward.isDefEq.respectTransparency false in
/-- Restriction preserves the Koszul-to-quotient comparison itself and both units.
Source: Stacks 099M, 0A0E (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the finite Koszul complexes are finite sums of the chosen representative with
identical differentials and transitions after restriction. Their augmentations to the
finite quotients are identical as well. Apply the strict derived-limit restriction
comparison to this square of towers. The resulting square is the displayed equation.
Every augmentation preserves the degree-zero element 1, giving both unit equations.
Alternatively the reflector universal property determines this same square uniquely. -/
theorem koszul_quotient_restriction [IsNoetherianRing A] (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = I) :
    ∃ (KR : KoszulPresentation J A I false r a) (KB : KoszulPresentation J A I true r a)
      (θR : koszulCompletion J A I KR ≅ completion J A I false)
      (θB : koszulCompletion J A I KB ≅ completion J A I true)
      (κ : dres (coefficientMap J A I) ⋙ koszulCompletion J A I KR ≅
        koszulCompletion J A I KB ⋙ dres (coefficientMap J A I))
      (χ : dres (coefficientMap J A I) ⋙ completion J A I false ≅
        completion J A I true ⋙ dres (coefficientMap J A I)),
      (∀ N : D (constant J A), koszulUnit J A I KR N ≫ θR.hom.app N =
        (completionUnit J A I false).app N) ∧
      (∀ M : D (completed J A I), koszulUnit J A I KB M ≫ θB.hom.app M =
        (completionUnit J A I true).app M) ∧
      (∀ M : D (completed J A I),
        koszulUnit J A I KR ((dres (coefficientMap J A I)).obj M) ≫ κ.hom.app M =
          (dres (coefficientMap J A I)).map (koszulUnit J A I KB M)) ∧
      (∀ M : D (completed J A I),
        (completionUnit J A I false).app ((dres (coefficientMap J A I)).obj M) ≫
          χ.hom.app M =
          (dres (coefficientMap J A I)).map ((completionUnit J A I true).app M)) ∧
      (∀ M : D (completed J A I),
        θR.hom.app ((dres (coefficientMap J A I)).obj M) ≫ χ.hom.app M =
          κ.hom.app M ≫ (dres (coefficientMap J A I)).map (θB.hom.app M)) := by
  obtain ⟨KR, ⟨θR, hR⟩, _⟩ := koszul_quotient_reflector J A I false r a ha
  obtain ⟨KB, ⟨θB, hB⟩, _⟩ := koszul_quotient_reflector J A I true r a ha
  obtain ⟨χ, hχ⟩ := completion_restriction J A I
  let F := dres (coefficientMap J A I)
  let κ : F ⋙ koszulCompletion J A I KR ≅ koszulCompletion J A I KB ⋙ F :=
    Functor.isoWhiskerLeft F θR ≪≫ χ ≪≫ Functor.isoWhiskerRight θB.symm F
  refine ⟨KR, KB, θR, θB, κ, χ, hR, hB, ?_, hχ, ?_⟩
  · intro M
    change koszulUnit J A I KR (F.obj M) ≫
      (θR.hom.app (F.obj M) ≫ χ.hom.app M ≫ F.map (θB.inv.app M)) = _
    rw [← Category.assoc, hR, ← Category.assoc, hχ, ← hB M, F.map_comp]
    simp only [Category.assoc, ← F.map_comp, θB.hom_inv_id_app, Category.comp_id]
    rfl
  · intro M
    change θR.hom.app (F.obj M) ≫ χ.hom.app M =
      (θR.hom.app (F.obj M) ≫ χ.hom.app M ≫ F.map (θB.inv.app M)) ≫
        F.map (θB.hom.app M)
    simp only [Category.assoc, ← F.map_comp, θB.inv_hom_id_app, F.map_id]
    exact congrArg (fun t ↦ θR.hom.app (F.obj M) ≫ t)
      (Category.comp_id (χ.hom.app M)).symm

end CategoryTheory.ConstantCompletion
