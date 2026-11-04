/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

set_option linter.privateModule false

/-! Tor-amplitude transport for the normalized smooth-purity reduction tower.
Source: blueprint latest, normalized-towers, uniform Tor and cohomological bounds.
(blueprint: lem-sp-reduction-tower-tor-intervals).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

private theorem integral_coefficient_iso :
    ∃ F : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (Mon.mk (spIntegralCondensed l E) ≅
        Mon.mk (Profinite.padicIntegersRingObj l F)) := by
  let f : E →ₐ[ℚ_[l]] PadicAlgCl l := IsAlgClosed.lift
  let F : PadicAlgCl.FiniteIntermediateField l :=
    ⟨f.fieldRange, f.equivFieldRange.toLinearEquiv.finiteDimensional⟩
  let : FiniteDimensional ℚ_[l] F := F.property
  let e : E ≃ₐ[ℚ_[l]] F := f.equivFieldRange
  let := spectralNorm.normedField ℚ_[l] E
  let := PadicAlgCl.normedFieldOfAlgebra l F
  have hn (x : E) : Padic.coefficientExtensionAbsoluteValue l E x = ‖f x‖ := by
    let a : AbsoluteValue E ℝ :=
      { toFun := fun x ↦ ‖f x‖
        map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
        nonneg' := fun x ↦ norm_nonneg _
        eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
        add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
    have ha (y : ℚ_[l]) : a (algebraMap ℚ_[l] E y) = ‖y‖ := by
      change ‖f (algebraMap ℚ_[l] E y)‖ = ‖y‖
      rw [f.commutes]
      exact PadicAlgCl.norm_extends l y
    exact (spectralNorm_unique_field_norm_ext ha x).symm
  have hm (x : E) : x ∈ Padic.coefficientExtensionIntegers l E ↔
      e x ∈ PadicAlgCl.integers l F := by
    have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.1 x
    rw [hn] at h
    exact h.trans (by
      rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
      rfl)
  let t : Padic.coefficientExtensionIntegers l E ≃+* PadicAlgCl.integers l F :=
    { toFun := fun x ↦ ⟨e x.val, (hm x.val).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x.val, (hm _).mpr (by
        simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x.val y.val)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x.val y.val) }
  have ht : Isometry t := by
    apply Isometry.of_dist_eq
    intro x y
    change ‖f x.val - f y.val‖ = Padic.coefficientExtensionAbsoluteValue l E (x.val - y.val)
    rw [← map_sub, hn]
  have hti : Continuous t.symm := (show _ ≃ᵢ _ from ⟨t.toEquiv, ht⟩).symm.continuous
  let q : Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers l E) ≅
      Profinite.padicIntegersCondensedRing.{u} l F :=
    { hom := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((t.toRingHom.compLeftContinuous _ ht.continuous).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      inv := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((t.symm.toRingHom.compLeftContinuous _ hti).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact t.symm_apply_apply (x.down z)
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact t.apply_symm_apply (x.down z) }
  let G := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)
  have : IsMonHom (G.mapIso q).hom :=
    Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) q.hom
  exact ⟨F, ⟨Mon.mkIso' (G.mapIso q)⟩⟩

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall in
/-- The bounded constructibility hypothesis already implies finite Tor amplitude.
Source: the integral clause of `det-def-localizing-closure-ctf-equals-bc`.
(blueprint: lem-sp-reduction-tower-tor-intervals). -/
private theorem sp_reduction_tower_finite_tor_amplitude
    [CompactSpace T] [QuasiSeparatedSpace T]
    (M : DerivedCategory (spIntegralSectionModules l E T))
    (hM : constantModelBoundedConstructible (spIntegralCondensed l E) T
      ((spIntegralInternalization l E T).obj M)) :
    DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (spIntegralCondensed l E) T))
      ((spIntegralInternalization l E T).obj M) := by
  obtain ⟨F, hF⟩ := integral_coefficient_iso l E
  have heq := (localizingClosure_ctf_equals_bc.{u} l T (spIntegralCondensed l E)
    (Or.inr (Or.inr (Or.inl ⟨F, Or.inl hF⟩)))).1.2.2.1
  have hmem : (constantModelBoundedConstructible (spIntegralCondensed l E) T ⊓
      DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2}
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (spIntegralCondensed l E) T)))
      ((spIntegralInternalization l E T).obj M) := by
    rw [heq]
    exact hM
  exact hmem.2

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall in
/-- Bounded constructible integral internalizations have finite Tor amplitude, and
all evaluated reductions preserve every specified ordered Tor interval.

Source: blueprint latest, sec-smooth-purity/sk-def-sp-normalized-towers/_section.md,
uniform bounds; the reduction argument of lem-sp-reduction-tower-tor-intervals;
Stacks Tags 06YY and 08FZ
(blueprint: lem-sp-reduction-tower-tor-amplitude-helper).

Proof:
1. Embed E into the fixed algebraic closure. Uniqueness of its extended norm identifies
its integer ring isometrically with that of a finite intermediate field. Continuous
functions induce the required condensed coefficient isomorphism. Apply the integral
qcqs clause of localizingClosure_ctf_equals_bc to hM to obtain finite Tor amplitude.
2. In a specified interval [a,b], choose a bounded flat internal representative P.
The exact section equivalence gives a representative Q of M, by its derived counit.
Its tensor comparison identifies flat terms with site-flat terms. Its zero terms
outside [a,b] are preserved by the additive equivalence, and Q is K-flat.
3. At level n, apply the recorded scalar model's ordinary extension to Q. Change of
rings preserves its flat terms and K-flatness; additivity preserves its zero terms.
The scalar model's counit computes derived extension on Q. Compose this isomorphism
with the supplied evaluation comparison and the image of Q isomorphic to M.
4. The resulting bounded flat model satisfies the intrinsic Tor predicate's tests for
all K-flat representatives, by scalarExtension_tor_flat_model. No flatness of the
quotient map, normalization condition, or geometric nonemptiness is required. -/
theorem sp_reduction_tower_tor_amplitude
    (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D)
    (evaluation : spReductionDerivedEvaluations l E T D coefficient red)
    [CompactSpace T] [QuasiSeparatedSpace T]
    (M : DerivedCategory (spIntegralSectionModules l E T))
    (hM : constantModelBoundedConstructible (spIntegralCondensed l E) T
      ((spIntegralInternalization l E T).obj M)) :
    DerivedCategory.finiteTorAmplitude.{u + 1, u + 1, u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (spIntegralCondensed l E) T))
      ((spIntegralInternalization l E T).obj M) ∧
    ∀ (a b : ℤ), a ≤ b →
      DerivedCategory.torAmplitudeIn.{u + 1, u + 1, u + 2}
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (spIntegralCondensed l E) T)) a b
        ((spIntegralInternalization l E T).obj M) →
      ∀ n : ℕ,
        Scheme.HasProEtaleTorAmplitude T
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
          ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)) a b := by
  classical
  refine ⟨sp_reduction_tower_finite_tor_amplitude l E T M hM, ?_⟩
  intro a b hab htor n
  let R := condensedRingObj (spIntegralCondensed l E) T
  let F := spIntegralModuleEquivalence l E T
  have : F.functor.Additive :=
    InternalAbelianSheafModule.comparison_additive (Scheme.ProEt.topology T) R
  have : F.inverse.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨P, hge, hle, hP, ⟨eP⟩⟩ :=
    (DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat.{u + 1, u + 1, u + 2} a b
      ((spIntegralInternalization l E T).obj M)).mp htor
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hflat, _⟩ :=
    InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology T) R
  let Q := (F.functor.mapHomologicalComplex (.up ℤ)).obj P
  have hQ : ∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology T)
      (R := spIntegralSectionRing l E T) (Q.X i) := by
    intro i
    exact (hflat (P.X i)).mp (hP i).2
  have : CochainComplex.IsStrictlyLE Q b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff _ _ b).mpr hle
  have hkQ := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (spIntegralSectionRing l E T) Q b hQ
  let eQ : DerivedCategory.Q.obj Q ≅ M :=
    (F.functor.mapDerivedCategoryFactors.app P).symm ≪≫
      F.functor.mapDerivedCategory.mapIso eP ≪≫ (F.mapDerivedCategory.counitIso.app M)
  let φ := spIntegralReductionScalar l E T coefficient n
  let S := (D.scalar φ).model
  have hext := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    φ Q S.E S.obj_eq (fun g ↦ S.map_eq g) hkQ
      (fun i ↦ (SheafOfModules.flat_to_cat (spIntegralSectionRing l E T) (Q.X i) (hQ i)).2)
  let V := (S.E.mapHomologicalComplex (.up ℤ)).obj Q
  have hV : ∀ i, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology T)
      (R := Scheme.proEtaleConstantRing T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)))
      (V.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ (V.X i)).symm (hext.2 i)
  have hbounds (i : ℤ) (hi : i < a ∨ b < i) : IsZero (V.X i) := by
    apply S.E.map_isZero
    apply F.functor.map_isZero
    rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE a i hi
    · exact P.isZero_of_isStrictlyLE b i hi
  have : IsIso (S.ε.app Q) := S.computes Q hkQ
  let eV : (spDerivedCoefficientEvaluation l E T D n).obj (red.obj M) ≅
      DerivedCategory.Q.obj V :=
    (evaluation n).app M ≪≫ S.T.mapIso eQ.symm ≪≫ asIso (S.ε.app Q)
  exact (scalarExtension_tor_flat_model T _ _ a b hab).mpr ⟨V, hV, hbounds, ⟨eV⟩⟩
end AlgebraicGeometry.ProEtale
