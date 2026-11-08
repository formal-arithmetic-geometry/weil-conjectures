/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Submission.WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Submission.WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
public import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Submission.WeilConjectures.Topology.ContinuousMapCondensedRing
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import Submission.WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Submission.WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import Submission.WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Submission.WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import Submission.WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import Submission.WeilConjectures.NumberTheory.Padics.IntegersModPow
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistLevels

import Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Filtered.Final
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistConstructions

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Coefficient extension maps, the field colimit and signed Tate twists

Source: blueprint `sk-def-sp-tate-twist`. The finite levels and integral and
rational objects are re-exported from `ProEtaleTateTwistLevels`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance 20000] HasLimitsOfShape.has_limit HasColimitsOfShape.has_colimit
attribute [local instance 20000] Sheaf.instHasLimitsOfShape AddCommGrpCat.hasLimitsOfShape

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local irreducible] spEllPointReduction spEllPointTransition

set_option backward.isDefEq.respectTransparency false in
private theorem spIntegersMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) : IsMonHom (spIntegersMap X ℓ h) ∧
      spIntegersMap X ℓ h ≫ padicIntegersToPadicSubfield X ℓ F =
        padicIntegersToPadicSubfield X ℓ E ≫
          coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X := by
  unfold spIntegersMap
  exact (spIntegersMap_existsUnique X ℓ h).exists.choose_spec

attribute [local irreducible] spIntegersMap

private theorem spEllReduction_isMonHom
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsMonHom (spEllReduction X ℓ E n) := by
  dsimp only [spEllReduction]
  infer_instance

attribute [local instance] spEllReduction_isMonHom

set_option backward.isDefEq.respectTransparency false in
private theorem spEllMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) (n : ℕ) : spEllReduction X ℓ E n ≫ spEllMap X ℓ h n =
      spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n := by
  unfold spEllMap
  exact (spEllMap_existsUnique X ℓ h n).exists.choose_spec

attribute [local irreducible] spEllMap

set_option backward.isDefEq.respectTransparency false in
private theorem spIntegralTwistMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) : ∀ n : ℕ, spIntegralTwistMap X ℓ h ≫
      (limit.π (spIntegralTwistSystem X ℓ F) (op n)).hom =
        (limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom ≫
          (spEllMap X ℓ h n ⊗ₘ
            𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) := by
  unfold spIntegralTwistMap
  exact (spIntegralTwistMap_existsUnique X ℓ h).exists.choose_spec

attribute [local irreducible] spIntegralTwistMap

private theorem spRationalTwistMap_spec {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E) ≫
        spRationalTwistMap X ℓ h =
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X ⊗ₘ
        spIntegralTwistMap X ℓ h) ≫
          Mod.extendπ (padicIntegersToPadicSubfield X ℓ F) (spIntegralTwist X ℓ F) := by
  unfold spRationalTwistMap
  exact (spRationalTwistMap_existsUnique X ℓ h).exists.choose_spec

attribute [local irreducible] spRationalTwistMap

/-- The identity inclusion induces the identity transition.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist).
Proof: identity maps have the required finite projections and localization formula.
Apply uniqueness first to the integral limits and then to the rational tensor quotient. -/
theorem spRationalTwistMap_id (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    spRationalTwistMap X ℓ (le_refl E) = 𝟙 _ := by
  have hc : coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ (le_refl E)) X =
      𝟙 _ := by
    rw [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id]
  have hi : spIntegersMap X ℓ (le_refl E) = 𝟙 _ := by
    apply (spIntegersMap_existsUnique X ℓ (le_refl E)).unique
      (spIntegersMap_spec X ℓ (le_refl E))
    exact ⟨inferInstance, by simp only [hc, Category.id_comp, Category.comp_id]⟩
  have he (n : ℕ) : spEllMap X ℓ (le_refl E) n = 𝟙 _ := by
    apply (spEllMap_existsUnique X ℓ (le_refl E) n).unique
      (spEllMap_spec X ℓ (le_refl E) n)
    simp only [hi, Category.id_comp, Category.comp_id]
  have ht : spIntegralTwistMap X ℓ (le_refl E) = 𝟙 _ := by
    apply (spIntegralTwistMap_existsUnique X ℓ (le_refl E)).unique
      (spIntegralTwistMap_spec X ℓ (le_refl E))
    intro n
    simp only [he, id_tensorHom_id]
    exact (Category.comp_id _).symm
  apply (spRationalTwistMap_existsUnique X ℓ (le_refl E)).unique
    (spRationalTwistMap_spec X ℓ (le_refl E))
  simp only [hc, ht, id_tensorHom_id, Category.id_comp]
  exact Category.comp_id _

private theorem spTensorNormalization_comp
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B D M N P U V W : C}
    (q₀ : A ⊗ M ⟶ U) (q₁ : B ⊗ N ⟶ V) (q₂ : D ⊗ P ⟶ W)
    (a : A ⟶ B) (b : B ⟶ D) (g : M ⟶ N) (h : N ⟶ P)
    (f : U ⟶ V) (k : V ⟶ W)
    (hf : q₀ ≫ f = (a ⊗ₘ g) ≫ q₁)
    (hk : q₁ ≫ k = (b ⊗ₘ h) ≫ q₂) :
    q₀ ≫ (f ≫ k) = ((a ≫ b) ⊗ₘ (g ≫ h)) ≫ q₂ := by
  rw [← Category.assoc, hf, Category.assoc, hk, ← Category.assoc,
    tensorHom_comp_tensorHom]

/-- Field-extension transitions compose.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist).
Proof: the two composites have the same maps on finite root tensors because the
coefficient inclusions compose. Joint injectivity of limit projections gives the
integral identity. The localization pure-tensor formula then gives the rational
identity, by uniqueness through the tensor coequalizer. -/
theorem spRationalTwistMap_comp {E F H : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) (k : F ≤ H) :
    spRationalTwistMap X ℓ (h.trans k) =
      spRationalTwistMap X ℓ h ≫ spRationalTwistMap X ℓ k := by
  let : HasLimit (spIntegralTwistSystem X ℓ E) := inferInstance
  let : HasLimit (spIntegralTwistSystem X ℓ F) := inferInstance
  let : HasLimit (spIntegralTwistSystem X ℓ H) := inferInstance
  have hc : coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ (h.trans k)) X =
      coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X ≫
        coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ k) X := by
    rw [Profinite.padicSubfieldRingObjMap_comp, coefficientMap_comp]
  have hm : spIntegersMap X ℓ (h.trans k) =
      spIntegersMap X ℓ h ≫ spIntegersMap X ℓ k := by
    have := (spIntegersMap_spec X ℓ h).1
    have := (spIntegersMap_spec X ℓ k).1
    apply (spIntegersMap_existsUnique X ℓ (h.trans k)).unique
      (spIntegersMap_spec X ℓ (h.trans k))
    refine ⟨inferInstance, ?_⟩
    calc
      _ = spIntegersMap X ℓ h ≫ (spIntegersMap X ℓ k ≫
          padicIntegersToPadicSubfield X ℓ H) := Category.assoc _ _ _
      _ = _ := by rw [(spIntegersMap_spec X ℓ k).2, ← Category.assoc, (spIntegersMap_spec X ℓ h).2,
        Category.assoc, ← hc]
  have hn (n : ℕ) : spEllMap X ℓ (h.trans k) n =
      spEllMap X ℓ h n ≫ spEllMap X ℓ k n := by
    apply (spEllMap_existsUnique X ℓ (h.trans k) n).unique (spEllMap_spec X ℓ (h.trans k) n)
    rw [← Category.assoc, spEllMap_spec X ℓ h n, Category.assoc, spEllMap_spec X ℓ k n,
      ← Category.assoc, ← hm]
  have hl : spIntegralTwistMap X ℓ (h.trans k) =
      spIntegralTwistMap X ℓ h ≫ spIntegralTwistMap X ℓ k := by
    apply (spIntegralTwistMap_existsUnique X ℓ (h.trans k)).unique
      (spIntegralTwistMap_spec X ℓ (h.trans k))
    intro n
    set_option backward.isDefEq.respectTransparency false in
    rw [Category.assoc, spIntegralTwistMap_spec X ℓ k n, ← Category.assoc,
      spIntegralTwistMap_spec X ℓ h n,
      Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, ← hn n]
  apply (spRationalTwistMap_existsUnique X ℓ (h.trans k)).unique
    (spRationalTwistMap_spec X ℓ (h.trans k))
  have hh := spTensorNormalization_comp
    (Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E))
    (Mod.extendπ (padicIntegersToPadicSubfield X ℓ F) (spIntegralTwist X ℓ F))
    (Mod.extendπ (padicIntegersToPadicSubfield X ℓ H) (spIntegralTwist X ℓ H))
    (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X)
    (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ k) X)
    (spIntegralTwistMap X ℓ h) (spIntegralTwistMap X ℓ k)
    (spRationalTwistMap X ℓ h) (spRationalTwistMap X ℓ k)
    (spRationalTwistMap_spec X ℓ h) (spRationalTwistMap_spec X ℓ k)
  set_option backward.isDefEq.respectTransparency false in
  simpa only [← hc, ← hl] using hh

attribute [local irreducible] spIntegralTwist spIntegralTwistSystem

set_option backward.isDefEq.respectTransparency true in
private theorem spExtend_semilinear
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [CategoryTheory.Limits.HasCoequalizers C]
    [∀ Z : C, CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S A B : C} [MonObj R] [MonObj S] [MonObj A] [MonObj B]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj A] [IsCommMonObj B]
    (p : R ⟶ A) [IsMonHom p] (q : S ⟶ B) [IsMonHom q]
    (c : A ⟶ B) [IsMonHom c] (M : Mod C R) (N : Mod C S)
    (g : M.X ⟶ N.X)
    (f : (Mod.extendScalarsObj p M).X ⟶ (Mod.extendScalarsObj q N).X)
    (hf : Mod.extendπ p M ≫ f = (c ⊗ₘ g) ≫ Mod.extendπ q N) :
    Mod.act (Mod.extendScalarsObj p M).X ≫ f =
      (c ⊗ₘ f) ≫ Mod.act (Mod.extendScalarsObj q N).X := by
  apply (cancel_epi (A ◁ Mod.extendπ p M)).mp
  rw [Mod.whiskerLeft_extendπ_smul_assoc, hf]
  calc
    _ = (α_ A A M.X).inv ≫ ((MonObj.mul ≫ c) ⊗ₘ g) ≫ Mod.extendπ q N := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp]
    _ = (α_ A A M.X).inv ≫ (((c ⊗ₘ c) ≫ MonObj.mul) ⊗ₘ g) ≫
        Mod.extendπ q N := by rw [IsMonHom.mul_hom]
    _ = (c ⊗ₘ (c ⊗ₘ g)) ≫ (α_ B B N.X).inv ≫
        MonObj.mul ▷ N.X ≫ Mod.extendπ q N := by
      rw [associator_inv_naturality_assoc]
      simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id]
    _ = (c ⊗ₘ (c ⊗ₘ g)) ≫ B ◁ Mod.extendπ q N ≫
        Mod.act (Mod.extendScalarsObj q N).X := by
      rw [Mod.whiskerLeft_extendπ_smul]
    _ = A ◁ Mod.extendπ p M ≫ (c ⊗ₘ f) ≫
        Mod.act (Mod.extendScalarsObj q N).X := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, Category.comp_id]
      rw [hf]

/-- The specified rational transitions are semilinear for the coefficient inclusions.
Source: blueprint scalar-action paragraph (blueprint: sk-def-sp-tate-twist).
Proof: each finite-level transition tensors a coefficient homomorphism with the
identity on roots, hence is semilinear. The integral limit projections jointly
reflect equality, so the integral map is semilinear. Apply the localization
normalization of spRationalTwistMap on pure tensors and cancel its epimorphic
projection to obtain the displayed action identity. -/
theorem spRationalTwistMap_semilinear {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    Mod.act (spRationalTwist X ℓ E).X ≫ spRationalTwistMap X ℓ h =
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X ⊗ₘ
        spRationalTwistMap X ℓ h) ≫ Mod.act (spRationalTwist X ℓ F).X := by
  exact spExtend_semilinear (padicIntegersToPadicSubfield X ℓ E)
    (padicIntegersToPadicSubfield X ℓ F)
    (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X)
    (spIntegralTwist X ℓ E) (spIntegralTwist X ℓ F)
    (spIntegralTwistMap X ℓ h) (spRationalTwistMap X ℓ h)
    (spRationalTwistMap_spec X ℓ h)

/-- The specified diagram of rational twists on the small directed poset of finite fields.
Source: blueprint algebraic-closure colimit (blueprint: sk-def-sp-tate-twist). -/
def spRationalTwistDiagram : PadicAlgCl.FiniteIntermediateField ℓ ⥤
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} where
  obj E := (spRationalTwist X ℓ E).X
  map f := spRationalTwistMap X ℓ (leOfHom f)
  map_id E := spRationalTwistMap_id X ℓ E
  map_comp f g := spRationalTwistMap_comp X ℓ (leOfHom f) (leOfHom g)

/-- The underlying algebraic-closure twist is the sheafified abelian colimit, not a
sectionwise union without sheafification.
Source: blueprint algebraic-closure colimit (blueprint: sk-def-sp-tate-twist). -/
def spQbarTwistAb : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  colimit (C := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (spRationalTwistDiagram X ℓ)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem spColimitModule
    {C I : Type*} [Category C] [MonoidalCategory C] [Category I] [IsSifted I]
    (A M : I ⥤ C) [∀ i, MonObj (A.obj i)] [∀ i, ModObj (A.obj i) (M.obj i)]
    (cA : Cocone A) (cM : Cocone M) (hA : IsColimit cA) (hM : IsColimit cM)
    [MonObj cA.pt]
    [hι : ∀ i, @IsMonHom C _ _ (A.obj i) cA.pt inferInstance inferInstance (cA.ι.app i)]
    [PreservesColimit M (tensorLeft (𝟙_ C))]
    [PreservesColimit₂ A A (curriedTensor C)]
    [PreservesColimit₂ A M (curriedTensor C)]
    [PreservesColimit₂ (A ⊗ A) M (curriedTensor C)]
    (hsemi : ∀ {i j} (f : i ⟶ j),
      (A.map f ⊗ₘ M.map f) ≫ Mod.act (M.obj j) = Mod.act (M.obj i) ≫ M.map f) :
    ∃! a : ModObj cA.pt cM.pt,
      ∀ i, (cA.ι.app i ⊗ₘ cM.ι.app i) ≫ a.smul =
        Mod.act (M.obj i) ≫ cM.ι.app i := by
  let ai (i : I) : A.obj i ⟶ cA.pt := cA.ι.app i
  let mi (i : I) : M.obj i ⟶ cM.pt := cM.ι.app i
  let : ∀ i, IsMonHom (ai i) := fun i ↦ hι i
  let τ : A ⊗ M ⟶ M :=
    { app i := Mod.act (M.obj i)
      naturality i j f := hsemi f }
  let c := (Cocone.precompose τ).obj cM
  let ht := hA.tensor hM
  obtain ⟨act, hact⟩ : ∃ act : cA.pt ⊗ cM.pt ⟶ cM.pt, ht.desc c = act := ⟨_, rfl⟩
  have ha (i : I) : (ai i ⊗ₘ mi i) ≫ act =
      Mod.act (M.obj i) ≫ mi i := by
    rw [← hact]
    exact ht.fac c i
  have hu : MonObj.one ▷ cM.pt ≫ act = (λ_ cM.pt).hom := by
    apply (isColimitOfPreserves (tensorLeft (𝟙_ C)) hM).hom_ext
    intro i
    change (𝟙_ C) ◁ mi i ≫ MonObj.one ▷ cM.pt ≫ act =
      (𝟙_ C) ◁ mi i ≫ (λ_ cM.pt).hom
    calc
      _ = (MonObj.one ⊗ₘ mi i) ≫ act := by
        simp only [MonoidalCategory.tensorHom_def', Category.assoc]
      _ = (MonObj.one ▷ M.obj i) ≫
          (ai i ⊗ₘ mi i) ≫ act := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          IsMonHom.one_hom, Category.id_comp]
      _ = (λ_ (M.obj i)).hom ≫ mi i := by
        rw [ha, Mod.one_act_assoc]
      _ = _ := (leftUnitor_naturality _).symm
  have hm : MonObj.mul ▷ cM.pt ≫ act =
      (α_ cA.pt cA.pt cM.pt).hom ≫ cA.pt ◁ act ≫ act := by
    apply ((hA.tensor hA).tensor hM).hom_ext
    intro i
    change ((ai i ⊗ₘ ai i) ⊗ₘ mi i) ≫
        MonObj.mul ▷ cM.pt ≫ act =
      ((ai i ⊗ₘ ai i) ⊗ₘ mi i) ≫
        (α_ cA.pt cA.pt cM.pt).hom ≫ cA.pt ◁ act ≫ act
    calc
      _ = (MonObj.mul ▷ M.obj i) ≫ (ai i ⊗ₘ mi i) ≫ act := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.comp_id, Category.id_comp, ← IsMonHom.mul_hom]
      _ = (α_ (A.obj i) (A.obj i) (M.obj i)).hom ≫
          A.obj i ◁ Mod.act (M.obj i) ≫ Mod.act (M.obj i) ≫ mi i := by
        rw [ha, Mod.mul_act_assoc]
      _ = _ := by
        rw [associator_naturality_assoc]
        simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.comp_id]
        rw [ha, ← ha]
        simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
        rw [ha]
  let a : ModObj cA.pt cM.pt :=
    { smul := act
      one_smul := hu
      mul_smul := hm }
  refine ⟨a, ?_, ?_⟩
  · intro i
    change (ai i ⊗ₘ mi i) ≫ act = Mod.act (M.obj i) ≫ mi i
    exact ha i
  intro a ha'
  apply ModObj.ext
  apply ht.hom_ext
  intro i
  exact (ha' i).trans (ha i).symm

/-- The colimit's action is uniquely determined by multiplying at a common finite field.
Source: blueprint scalar-action paragraph (blueprint: sk-def-sp-tate-twist).
Proof: on sectionwise presheaf colimits choose a common finite extension H of E and F.
Multiply the two images there. The tensor normalization of the rational transitions
makes them semilinear, so further extension preserves this product. Any two common
extensions map into their finite compositum, giving independence of representatives.
The module identities hold at a common field. Sheafify the action. The coefficient
colimit is p_X^* Qbar by the sectionwise finite-subextension union and preservation
of colimits by the left adjoint p_X^*. Tensor preserves colimits and sheafification,
so the stagewise formulas uniquely determine the resulting action. -/
theorem spQbarTwistAction_existsUnique :
    ∃! a : ModObj (condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} ℓ) X) (spQbarTwistAb X ℓ),
      ∀ (E F H : PadicAlgCl.FiniteIntermediateField ℓ) (hE : E ≤ H) (hF : F ≤ H),
        (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X ⊗ₘ
          colimit.ι (spRationalTwistDiagram X ℓ) F) ≫ a.smul =
        (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ hE) X ⊗ₘ
          spRationalTwistMap X ℓ hF) ≫
            Mod.act (spRationalTwist X ℓ H).X ≫
              colimit.ι (spRationalTwistDiagram X ℓ) H := by
  let A := Profinite.padicSubfieldRingObjFunctor.{u} ℓ ⋙ upperStarFromPoint X
  let M := spRationalTwistDiagram X ℓ
  let cA := (upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone ℓ)
  let cM := colimit.cocone M
  let : IsSifted (PadicAlgCl.FiniteIntermediateField ℓ) := IsFiltered.isSifted
  let : ∀ E, MonObj (A.obj E) := by
    change ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      MonObj (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X)
    infer_instance
  let : ∀ E, ModObj (A.obj E) (M.obj E) := by
    change ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      ModObj (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X)
        (spRationalTwist X ℓ E).X
    exact fun E ↦ (spRationalTwist X ℓ E).mod
  let : MonObj cA.pt := by
    change MonObj (condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} ℓ) X)
    infer_instance
  let : ∀ E, @IsMonHom _ _ _ (A.obj E) cA.pt inferInstance inferInstance
      (cA.ι.app E) := by
    intro E
    change IsMonHom
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)
    infer_instance
  have hsemi {E F : PadicAlgCl.FiniteIntermediateField ℓ} (f : E ⟶ F) :
      (A.map f ⊗ₘ M.map f) ≫ Mod.act (M.obj F) =
        Mod.act (M.obj E) ≫ M.map f :=
    (spRationalTwistMap_semilinear X ℓ (leOfHom f)).symm
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).isLeftAdjoint
  have hA : IsColimit cA := isColimitOfPreserves (upperStarFromPoint X)
    (Profinite.isColimitPadicAlgClRingObjCocone ℓ)
  obtain ⟨a, ha, hu⟩ := spColimitModule A M cA cM hA (colimit.isColimit M) hsemi
  refine ⟨a, ?_, ?_⟩
  · intro E F H hE hF
    have hcoeff : A.map (homOfLE hE) ≫ cA.ι.app H = cA.ι.app E := by
      simpa only [Category.comp_id] using cA.w (homOfLE hE)
    have htwist : M.map (homOfLE hF) ≫ cM.ι.app H = cM.ι.app F := by
      simpa only [Category.comp_id] using cM.w (homOfLE hF)
    change (cA.ι.app E ⊗ₘ cM.ι.app F) ≫ a.smul =
      (A.map (homOfLE hE) ⊗ₘ M.map (homOfLE hF)) ≫
        Mod.act (M.obj H) ≫ cM.ι.app H
    rw [← hcoeff, ← htwist, ← tensorHom_comp_tensorHom_assoc, ha H]
  · intro b hb
    apply hu
    intro E
    change (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X ⊗ₘ
      colimit.ι (spRationalTwistDiagram X ℓ) E) ≫ b.smul =
        Mod.act (spRationalTwist X ℓ E).X ≫ colimit.ι (spRationalTwistDiagram X ℓ) E
    simpa only [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id,
      spRationalTwistMap_id, id_tensorHom_id, Category.id_comp] using
      hb E E E (le_refl E) (le_refl E)

/-- Qbar_X(1), with the uniquely specified action on its sheafified colimit.
Source: blueprint algebraic-closure colimit and action (blueprint: sk-def-sp-tate-twist). -/
def spQbarTwist : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} ℓ) X) :=
  { X := spQbarTwistAb X ℓ
    mod := (spQbarTwistAction_existsUnique X ℓ).exists.choose }

end AlgebraicGeometry.ProEtale
