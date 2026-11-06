/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible

import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductions
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.SixFunctors.QcqsIntegralFiniteModelCompleteness
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralContinuousEncodingConstructible
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteConstantModelsCommonStratification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteConstantModelStrataGeneration
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Nonfinite-coefficient compactness from finite base cohomological dimension

This is the nonfinite-coefficient compactness input needed by the corrected Brown theorem.
The adopted source currently records the corresponding compactness declarations over finite
or separably closed fields; this theorem isolates the finite-cd extension.
(blueprint: lem-sfb-brown-finite-cd-integral-ext)
-/

@[expose] public section

set_option autoImplicit false

attribute [-instance] WeilConjectures.strictDvrSiteSmall
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

section

-- Use the same coefficient-point tensor instance as the finite-reduction theorem.
private noncomputable abbrev nativeCondensedMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall Ab
    (coherentTopology Profinite.{u})

attribute [local instance 40000] nativeCondensedMonoidal

private theorem hom_shift_product_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (Q : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (r : ℤ) (h : ∀ n, Subsingleton (Q ⟶ (K n) ⟦r⟧))
    (f : Q ⟶ (∏ᶜ K) ⟦r⟧) : f = 0 := by
  apply (isLimitOfPreserves (shiftFunctor (DerivedCategory C) r)
    (productIsProduct K)).hom_ext
  intro n
  exact (h n.as).elim _ _

/-- Vanishing in two adjacent degrees propagates from the levels to their Roos limit.
Source: the final paragraph of the integral Ext-bound proof and Stacks Tag 0149. -/
private theorem hom_roos_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (Q N : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (step : ∀ n, K (n + 1) ⟶ K n)
    (pN : N ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ N⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle step N pN δ) (q : ℤ)
    (hprev : ∀ n, Subsingleton (Q ⟶ (K n) ⟦q - 1⟧))
    (hnext : ∀ n, Subsingleton (Q ⟶ (K n) ⟦q⟧)) :
    Subsingleton (Q ⟶ N⟦q⟧) := by
  let T := CategoryTheory.Pretriangulated.Triangle.mk pN (towerTransitionEndomorphism step) δ
  have hT' : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles
      (C := DerivedCategory C) := hT
  let U := (shiftFunctor (CategoryTheory.Pretriangulated.Triangle (DerivedCategory C))
    (q - 1)).obj T
  have hU : U ∈ CategoryTheory.Pretriangulated.distinguishedTriangles (C := DerivedCategory C) :=
    CategoryTheory.Pretriangulated.Triangle.shift_distinguished T hT' (q - 1)
  let e := (shiftFunctorAdd' (DerivedCategory C) (q - 1) 1 q (by omega)).app N
  have hz (f : Q ⟶ N⟦q⟧) : f = 0 := by
    obtain ⟨g, hg⟩ := CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₁ U hU
      (f ≫ e.hom) (by
        apply (cancel_mono
          ((shiftFunctorAdd' (DerivedCategory C) (q - 1) 1 q (by omega)).app (∏ᶜ K)).inv).1
        rw [zero_comp]
        exact hom_shift_product_zero Q K q hnext _)
    have hg0 : g = 0 := hom_shift_product_zero Q K (q - 1) hprev g
    apply (cancel_mono e.hom).1
    simpa only [hg0, zero_comp] using hg
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

private theorem subsingleton_of_all_eq {α : Sort*} (z : α) (h : ∀ x, x = z) :
    Subsingleton α :=
  ⟨fun x y ↦ (h x).trans (h y).symm⟩

private def UniformHomBound {C : Type*} [Category C] [HasShift C ℤ]
    (P : C → Prop) (A : C) : Prop :=
  ∃ d : ℕ, ∀ N, P N → ∀ r : ℤ, (d : ℤ) < r → Subsingleton (A ⟶ N⟦r⟧)

private theorem uniformHomBound_iso
    {C : Type*} [Category C] [HasShift C ℤ] (P : C → Prop)
    {A B : C} (e : A ≅ B) (h : UniformHomBound P A) : UniformHomBound P B := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun N hN r hr ↦ ⟨fun f g ↦ ?_⟩⟩
  apply (cancel_epi e.hom).1
  exact (hd N hN r hr).elim _ _

private theorem uniformHomBound_zero
    {C : Type*} [Category C] [HasShift C ℤ] [HasZeroMorphisms C]
    (P : C → Prop) {A : C} (h : IsZero A) : UniformHomBound P A := by
  exact ⟨0, fun _ _ _ _ ↦ ⟨fun f g ↦ h.eq_of_src f g⟩⟩

private theorem uniformHomBound_extension
    {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : C → Prop) (T : Pretriangulated.Triangle C)
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (h₁ : UniformHomBound P T.obj₁) (h₃ : UniformHomBound P T.obj₃) :
    UniformHomBound P T.obj₂ := by
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₃, hd₃⟩ := h₃
  refine ⟨max d₁ d₃, fun N hN r hr ↦ ?_⟩
  have h₁ := hd₁ N hN r (lt_of_le_of_lt (by exact_mod_cast le_max_left d₁ d₃) hr)
  have h₃ := hd₃ N hN r (lt_of_le_of_lt (by exact_mod_cast le_max_right d₁ d₃) hr)
  have hz (f : T.obj₂ ⟶ N⟦r⟧) : f = 0 := by
    obtain ⟨g, hg⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f (h₁.elim _ _)
    rw [hg, h₃.elim g 0, comp_zero]
  exact ⟨fun f g ↦ (hz f).trans (hz g).symm⟩

private def reductionBound
    (X Z S : Scheme.{u}) (i : Z ⟶ X) (v : S ⟶ Z) [IsOpenImmersion v]
    (r : ℤ)
    (a : Arrow (CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))) : Prop :=
  match a with
  | ⟨@CommMon.mk _ _ _ _ Λ mΛ cΛ, @CommMon.mk _ _ _ _ Γ mΓ cΓ,
      ⟨@Mon.Hom.mk _ _ _ _ _ φ hφ⟩⟩ =>
    letI := mΛ
    letI := mΓ
    letI := cΛ
    letI := cΓ
    let φ' : Λ ⟶ Γ := φ
    letI : IsMonHom φ' := hφ
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
    letI : IsCommMonObj (condensedRingObj Λ X) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X)
    letI : IsCommMonObj (condensedRingObj Γ X) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X)
    ∀ (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj Λ S)), HasFiniteConstantLocalModel Λ S L →
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)), IsConstantModelConstructible Λ X N →
    ∀ f : (DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ i).obj
          ((CondensedRing.openImmersionLowerShriek Λ v).obj L)) ⟶
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (Λ := Λ) (Λ' := Γ) φ' X)).mapDerivedCategory.obj
          ((Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (coefficientMap (Λ := Λ) (Λ' := Γ) φ' X)).leftDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj N)))⟦r⟧, f = 0

private noncomputable def coefficientArrow
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    Arrow (CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :=
  Arrow.mk (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) (Mon.ofHom f))

private noncomputable def continuousArrow
    (A B : Type u) [CommRing A] [CommRing B]
    (tA : TopologicalSpace A) (tB : TopologicalSpace B)
    (hA : @IsTopologicalRing A tA _) (hB : @IsTopologicalRing B tB _)
    (f : A →+* B) (hf : @Continuous A B tA tB f) :
    Arrow (CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :=
  letI := tA
  letI := tB
  letI := hA
  letI := hB
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) :=
    Sheaf.monObj_sheafCompose_obj _ (Profinite.continuousMapRingSheafOfUniverse A)
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} B) :=
    Sheaf.monObj_sheafCompose_obj _ (Profinite.continuousMapRingSheafOfUniverse B)
  letI : IsCommMonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) :=
    Profinite.isCommMonObj_continuousMapRingObjOfUniverse A
  letI : IsCommMonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} B) :=
    Profinite.isCommMonObj_continuousMapRingObjOfUniverse B
  letI : IsMonHom (Profinite.continuousMapRingObjMapOfUniverse.{u, u} f hf) :=
    Sheaf.isMonHom_sheafCompose_map _ (Profinite.continuousMapRingSheafMapOfUniverse f hf)
  coefficientArrow (Profinite.continuousMapRingObjMapOfUniverse f hf)
private theorem continuousArrow_eq
    (A B : Type u) [CommRing A] [CommRing B]
    (tA tA' : TopologicalSpace A) (tB tB' : TopologicalSpace B)
    (ha : tA = tA') (hb : tB = tB')
    (hA : @IsTopologicalRing A tA _) (hA' : @IsTopologicalRing A tA' _)
    (hB : @IsTopologicalRing B tB _) (hB' : @IsTopologicalRing B tB' _)
    (f : A →+* B) (hf : @Continuous A B tA tB f)
    (hf' : @Continuous A B tA' tB' f) :
    continuousArrow A B tA tB hA hB f hf =
      continuousArrow A B tA' tB' hA' hB' f hf' := by
  subst tA'
  subst tB'
  rfl
private theorem reductionArrow_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    coefficientArrow (IntegralQuotient.reduction l E n) =
      coefficientArrow (DerivedNakayama.reductionRing l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have ht := DerivedNakayama.coefficientTopology l E
  have hi := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced
      (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hd : AdicCompletion.finiteTopology l E (n + 1) = ⊥ :=
    @DiscreteTopology.eq_bot _ _ (DerivedNakayama.quotientDiscrete l E (n + 1))
  exact continuousArrow_eq _ _ _ _ _ _ hi hd.symm
    (by let := spectralNorm.normedField (Padic l) E; infer_instance)
    (by infer_instance) (by infer_instance) (by infer_instance)
    _ (IntegralQuotient.reduction_continuous l E n) continuous_quot_mk

set_option maxHeartbeats 2000000 in
-- Kernel checking unfolds both scalar-change functors in the coefficient-arrow transport.

attribute [local instance 40000] AdicCompletion.ringMonoidalObject
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.modulesDerived
  AdicCompletion.finiteModulesDerived AdicCompletion.modulesMonoidal

set_option maxHeartbeats 2000000 in
-- Compare the finite-bound presentation with the native completion-level API once.

private theorem hom_roos_iso_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (A N Q : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (step : ∀ n, K (n + 1) ⟶ K n)
    (p : Q ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ Q⟦(1 : ℤ)⟧)
    (htri : IsDerivedLimitTriangle step Q p δ) (e : N ≅ Q) (r : ℤ)
    (hprev : ∀ n, Subsingleton (A ⟶ K n⟦r - 1⟧))
    (hnext : ∀ n, Subsingleton (A ⟶ K n⟦r⟧)) :
    Subsingleton (A ⟶ N⟦r⟧) := by
  have hQ := hom_roos_zero A Q K step p δ htri r hprev hnext
  exact ⟨fun f g ↦ by
    apply (cancel_mono ((shiftFunctor _ r).mapIso e).hom).mp
    exact hQ.elim _ _⟩

-- Comparing the native Roos levels with the scalar-change bounds unfolds large functors.

end

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

-- The derived coefficient equivalence compares large canonical single-functor constructions.
end CategoryTheory
