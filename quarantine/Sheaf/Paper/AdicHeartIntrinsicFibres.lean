/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.AdicHeartPullbackFibres
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.Paper.CoefficientHeartClosure
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.Paper.CompletedPullbackTriangles
import Sheaf.Paper.ContinuousAffineEtaleLattice
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.IntegralPullbackCompletedComparison
import Sheaf.Paper.IntegralTStructure
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.Paper.LisseIntegralSmallCoefficients
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.Paper.LocalizedTStructure
import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcScalarExtension
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Adic coefficient fibres in the intrinsic coefficient presentation

Source: Bhatt--Scholze, Section 6.8, especially Propositions 6.8.4 and 6.8.14
(blueprint: lem-per-adic-heart-pullback-fibres).
The original module supplies the raw completed-coefficient statements unchanged.
The declarations below transport their actual section normalization to the intrinsic
rational and common-stage categories used by the constructible Weil heart.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarDescent
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C]
    {D : Type*} [Category D] (p : R) (F : C ⥤ D)
    (hF : (Rationalization.W (Submonoid.powers p) C).IsInvertedBy F) :
    ∃! G : ScalarLocalization R C p ⥤ D,
      ScalarLocalization.localization R C p ⋙ G = F := by
  let M := Submonoid.powers p
  let H : ScalarLocalization R C p ⥤ Rationalization M C := {
    obj X := (Rationalization.Q M C).obj X.obj
    map {X Y} f := Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj f
    map_id X := by
      change Rationalization.tensorHomEquiv M (Localization.Away p) _ _
        (1 ⊗ₜ[R] 𝟙 X.obj) = _
      simp
    map_comp {X Y Z} f g := by
      induction f using TensorProduct.induction_on with
      | zero => simp
      | tmul a f =>
        induction g using TensorProduct.induction_on with
        | zero => simp
        | tmul b g =>
          change Rationalization.tensorHomEquiv M (Localization.Away p) _ _
            (ScalarLocalization.composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
          simp [ScalarLocalization.composition_tmul, Linear.smul_comp,
            Linear.comp_smul, smul_smul, mul_comm]
        | add g h hg hh =>
          rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
          simpa only [map_add, hg, hh] using
            (Preadditive.comp_add _ _ _ _ _ _).symm
      | add f h hf hh =>
        rw [Preadditive.add_comp X Y Z f h g]
        simpa only [map_add, hf, hh] using
          (Preadditive.add_comp _ _ _ _ _ _).symm }
  have : H.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : H.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  let e := Localization.Construction.objEquiv (Rationalization.W M C)
  have he (X : Rationalization M C) : H.obj ⟨e.symm X⟩ = X := e.apply_symm_apply X
  let J : Rationalization M C ⥤ ScalarLocalization R C p := {
    obj X := ⟨e.symm X⟩
    map {X Y} f := H.preimage (eqToHom (he X) ≫ f ≫ eqToHom (he Y).symm)
    map_id X := by apply H.map_injective; simp
    map_comp f g := by apply H.map_injective; simp }
  have hHJ : H ⋙ J = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change H.preimage _ = f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact H.preimage_map f
  have hQH : ScalarLocalization.localization R C p ⋙ H = Rationalization.Q M C := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change Rationalization.tensorHomEquiv M (Localization.Away p) _ _ (1 ⊗ₜ[R] f) = _
    simp
  have hQJ : Rationalization.Q M C ⋙ J = ScalarLocalization.localization R C p := by
    rw [← hQH, Functor.assoc, hHJ]
    rfl
  let G := Localization.Construction.lift F hF
  have hG : Rationalization.Q M C ⋙ G = F := Localization.Construction.fac F hF
  refine ⟨H ⋙ G, ?_, ?_⟩
  · change ScalarLocalization.localization R C p ⋙ (H ⋙ G) = F
    rw [← Functor.assoc, hQH, hG]
  · intro K hK
    have he : J ⋙ K = G := Localization.Construction.uniq _ _ (by
      rw [← Functor.assoc, hQJ, hK, hG])
    rw [← he, ← Functor.assoc, hHJ]
    rfl

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (W : Scheme.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ W)

/-- Completed geometric pullback, H⁰, point sections, then inversion of the uniformizer.
The coefficient-model equivalence is the published constant-section-normalized one.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def sfAdicIntegralFiber : sfIntegralConstructibleCategory l E W ⥤ ModuleCat.{u + 1} E :=
  (sfIntegralConstructible l E W).ι ⋙ (purCoefficientModel l E W).inverse ⋙
    pbcActualCompletedPull x (pbcIntegralDatum l E) ⋙
    DerivedCategory.homologyFunctor _ 0 ⋙ PerAdic.pointSections l E Ω ⋙
    ModuleCat.extendScalars (PerAdic.integerToField l E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedSectionVars false in
/-- Unique descent of actual completed sections along raw rationalization.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: the coefficient-model equivalence identifies these sections with integralFiber
of the original module. Uniformizer multiplication becomes invertible over E.
The scalar-localization universal property gives the unique extension, including its
fraction maps; a fraction f/ϖⁿ acts as ϖ⁻ⁿ times the map of completed point sections. -/
theorem sfAdicRationalFiber_existsUnique :
    ∃! F : sfRationalConstructibleCategory l E W ⥤ ModuleCat.{u + 1} E,
      sfRationalConstructibleLocalization l E W ⋙ F = sfAdicIntegralFiber l E W x := by
  have : (SheafOfModules.evaluation
      ((Spec (.of Ω)).adicLisseForget.obj
        (pbcAdicCompletion (Spec (.of Ω)) (pbcIntegralDatum l E)))
      (Opposite.op (ProEt.mk (𝟙 (Spec (.of Ω)))))).Additive := ⟨by intros; rfl⟩
  have : (PerAdic.pointSections l E Ω).Additive := by
    unfold PerAdic.pointSections
    infer_instance
  have := (integralDetailedCoefficientRestriction_exact W l E).1
  have := (integralDetailedCoefficientRestriction_exact W l E).2
  have : (integralDetailedTransport W l E).Additive := by
    dsimp [integralDetailedTransport]
    infer_instance
  have : (ModuleCat.extendScalars (PerAdic.integerToField l E)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u}
      (PerAdic.integerToField l E)).left_adjoint_additive
  have hadd : (sfAdicIntegralFiber l E W x).Additive := by
    change ((sfIntegralConstructible l E W).ι ⋙ integralDetailedTransport W l E ⋙ _).Additive
    infer_instance
  apply scalarDescent
  intro K L f hf
  obtain ⟨m, hm, t, ht⟩ := Rationalization.exists_comp_eq_smul_id hf
  have hdiv : Padic.coefficientExtensionUniformizer l E ∣
      (l : Padic.coefficientExtensionIntegers l E) := by
    let H := Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := Padic l) (L := E))
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
      H.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    apply Ideal.mem_span_singleton.mp
    rw [hgen]
    have hm : ∀ y : Padic.coefficientExtensionIntegers l E,
        y ∈ Padic.coefficientExtensionMaximalIdeal l E ↔
          Padic.coefficientExtensionAbsoluteValue l E (y : E) < 1 :=
      H.choose_spec.choose_spec.2.1
    apply (hm _).2
    change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
    have hh := spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)
    rw [map_natCast] at hh
    exact hh.trans_lt (Padic.norm_p_lt_one (p := l))
  have hscalar (m : Padic.coefficientExtensionIntegers l E)
      (hm : m ∈ Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
      (K : sfIntegralConstructibleCategory l E W) :
      IsIso ((sfAdicIntegralFiber l E W x).map (m • 𝟙 K)) := by
    obtain ⟨n, rfl⟩ := hm
    obtain ⟨a, ha⟩ := pow_dvd_pow_of_dvd hdiv n
    let F := sfAdicIntegralFiber l E W x
    have hl : (l ^ n : E) ≠ 0 := by
      have hl' : (l : Padic l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
      have : (l : E) ≠ 0 := by
        simpa using (map_ne_zero (algebraMap (Padic l) E)).2 hl'
      exact pow_ne_zero _ this
    have hi : IsIso ((l ^ n : E) • 𝟙 (F.obj K)) := by
      refine ⟨⟨(l ^ n : E)⁻¹ • 𝟙 _, ?_, ?_⟩⟩ <;>
        simp [Linear.comp_smul, smul_smul, hl]
    have hc : F.map ((Padic.coefficientExtensionUniformizer l E ^ n) • 𝟙 K) ≫
        F.map (a • 𝟙 K) = (l ^ n : E) • 𝟙 (F.obj K) := by
      rw [← F.map_comp]
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
      rw [mul_comm a, ← ha]
      simp [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, F.map_nsmul]
    have hc' : F.map (a • 𝟙 K) ≫
        F.map ((Padic.coefficientExtensionUniformizer l E ^ n) • 𝟙 K) =
        (l ^ n : E) • 𝟙 (F.obj K) := by
      rw [← F.map_comp]
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
      rw [← ha]
      simp [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, F.map_nsmul]
    have := mono_of_mono_fac hc
    have := epi_of_epi_fac hc'
    exact isIso_of_mono_of_epi _
  have hiso := hscalar m hm K
  have hcomp : IsIso ((sfAdicIntegralFiber l E W x).map f ≫
      (sfAdicIntegralFiber l E W x).map t) := by
    rw [← Functor.map_comp, ht]
    exact hiso
  have hmono : Mono ((sfAdicIntegralFiber l E W x).map f) :=
    mono_of_mono (sfAdicIntegralFiber l E W x |>.map f)
      (sfAdicIntegralFiber l E W x |>.map t)
  obtain ⟨Z, g, h, hT, m', hm', hZ⟩ := hf
  obtain ⟨r, hr⟩ := CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂ _ hT
    (m' • 𝟙 L) (by
      change (m' • 𝟙 L) ≫ g = 0
      rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id g,
        ← Linear.comp_smul, hZ, comp_zero])
  change m' • 𝟙 L = r ≫ f at hr
  have hcomp' : IsIso ((sfAdicIntegralFiber l E W x).map r ≫
      (sfAdicIntegralFiber l E W x).map f) := by
    rw [← Functor.map_comp, ← hr]
    exact hscalar m' hm' L
  have hepi : Epi ((sfAdicIntegralFiber l E W x).map f) :=
    epi_of_epi (sfAdicIntegralFiber l E W x |>.map r)
      (sfAdicIntegralFiber l E W x |>.map f)
  exact isIso_of_mono_of_epi _

/-- The rational fibre fixed by its section and fraction normalization.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def sfAdicRationalFiber : sfRationalConstructibleCategory l E W ⥤ ModuleCat.{u + 1} E :=
  (sfAdicRationalFiber_existsUnique l E W x).exists.choose

variable (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]

/-- The actual inclusion of a finite coefficient field, with its canonical small model.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def sfAdicCoefficientEmbedding (L : Padic.FiniteCoefficientFields l Qbar) :
    AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L →+* Qbar :=
  L.val.subtype.comp (Shrink.algEquiv (Padic l) L.val).toRingHom

/-- Finite-stage normalization of an adic common-stage fibre. The comparisons are
natural in every rational arrow, including all fractions. Scalar extension is the
ordinary tensor extension along the actual finite-field inclusion.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def SfAdicCommonFiberSpec
    (F : generalAlgebraicallyClosedConstructibleCategory l Qbar W ⥤
      ModuleCat.{max (u + 1) v} Qbar) : Prop :=
  ∀ L : Padic.FiniteCoefficientFields l Qbar,
    Nonempty (GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙ F ≅
      sfAdicRationalFiber l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) W x ⋙
        ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Qbar L))

/-- The existing adic fibre also exists in the intrinsic common-stage presentation.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: the normalized coefficient-model equivalences identify the two integral
presentations, their quotient transitions, and completed point sections. Rationalize
these equivalences using their fraction formulas. Their scalar-tensor comparisons
satisfy the tensor associativity and identity equations, so descend through the
common-stage quotient. Transport the fibre in CommonFiberAssertions along this
comparison. Its finite-stage comparisons are exactly those displayed here. -/
theorem sfAdicCommonFiber_exists :
    ∃ F : generalAlgebraicallyClosedConstructibleCategory l Qbar W ⥤
      ModuleCat.{max (u + 1) v} Qbar, SfAdicCommonFiberSpec l W x Qbar F := by
  sorry


variable {k : Type u} [Field k] [Fact (IsUnit (l : k))]
open PerAdic

/-- All clauses of the recorded adic-heart theorem, with its intrinsic-presentation
coefficient fibres made available as well. The first twelve conjuncts retain the
original raw-category theorem verbatim; the last clause changes only presentation.
Source: BS 6.8.2--6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: construct the integral standard t-structure from good truncations and
cohomology, then rationalize its classes and truncations. Compute completed pullback
on flat representatives; its quotient reductions preserve constructibility and
bounds. Evaluate strict quotient fibres on common finite lisse stratifications and
take their inverse limits, then invert the uniformizer. Lisse representation fibres
are exact and detect zero; finite scalar tensor commutes with their inverse limits.
These comparisons descend to common stages, retaining scalar associativity, identity,
and pullback comparisons. Fibre rank is locally constant on each lisse stratum, so
the nonzero-fibre locus is constructible. These are precisely steps 1--10 of
adicHeartPullbackFibres in the imported module. Finally apply the normalized
coefficient-model equivalence, as in sfAdicRationalFiber_existsUnique and
sfAdicCommonFiber_exists, to express those same fibres in the intrinsic categories. -/
theorem sfAdicHeartPullbackFibres (L : Padic.FiniteCoefficientFields l Qbar)
    (V T : Base k) (h : V.scheme ⟶ T.scheme) :
    (∀ W : Base k, RationalStandardAssertions l (pbcFiniteField.{u} l Qbar L) W) ∧
    RationalPullAssertions l (pbcFiniteField.{u} l Qbar L) V T h ∧
    RationalFiberAssertions (k := k) l (pbcFiniteField.{u} l Qbar L) ∧
    RationalComparisonAssertions l (pbcFiniteField.{u} l Qbar L) V T h ∧
    RationalSupportAssertions (k := k) l (pbcFiniteField.{u} l Qbar L) ∧
    RationalLimitAssertions (k := k) l (pbcFiniteField.{u} l Qbar L) ∧
    ScalarAssertions (k := k) l Qbar ∧
    ScalarFiberAssertions (k := k) l Qbar ∧
    ScalarPullbackFiberAssertions l Qbar V T h ∧
    CommonStandardAssertions (k := k) l Qbar ∧
    CommonPullAssertions l Qbar V T h ∧
    CommonFiberAssertions l Qbar V T h ∧
    ∀ (W : Base k) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ W.scheme),
      ∃ F : generalAlgebraicallyClosedConstructibleCategory l Qbar W.scheme ⥤
        ModuleCat.{max (u + 1) v} Qbar, SfAdicCommonFiberSpec l W.scheme x Qbar F := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
    adicHeartPullbackFibres l Qbar L V T h
  refine ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, ?_⟩
  intro W Ω _ _ x
  exact sfAdicCommonFiber_exists l W.scheme x Qbar

end WeilConjectures
