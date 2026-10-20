/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.CoefficientDuality
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import Sheaf.CategoryTheory.DerivedCategory.DualizingComplexBoundedDuality
import Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly
import WeilConjectures.RingTheory.DiscreteValuationRing.QuotientDuality
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable
import WeilConjectures.CategoryTheory.ObjectProperty.Duality
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr

/-! # Coefficient biduality at the finite, integral and field stages

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-weil-coefficient-frobenius; Stacks Tags 0AVF, 066Z and 07VI
(blueprint: lem-weil-coefficient-frobenius).

Ordinary duals are algebraic module duals. Finite means finitely generated.
The integral ordinary assertion is deliberately different from the derived assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace WeilConjectures

@[instance_reducible]
private noncomputable def coefficientBraided (R : Type u) [CommRing R] :
    BraidedCategory (DerivedCategory (ModuleCat.{u} R)) :=
  DerivedCategory.braidedCategory' (ModuleCat.{u} R)

private lemma coefficient_eval_eq (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) :
    coefficientDerivedEvaluation K =
      @MonoidalClosed.toIhomIhomUnit _ _ _ (coefficientBraided R) _ K := rfl

attribute [local irreducible] DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

private lemma scalar_unit_iso {C : Type*} [Category C]
    [MonoidalCategory C] [MonoidalClosed C] :
    IsIso (MonoidalClosed.curry (ρ_ (𝟙_ C)).hom) := by
  rw [← unitors_equal]
  have h : MonoidalClosed.curry (λ_ (𝟙_ C)).hom =
      (MonoidalClosed.unitNatIso.app (𝟙_ C)).hom := by
    simp [MonoidalClosed.unitNatIso, MonoidalClosed.curry_eq,
      conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  rw [h]
  infer_instance

private lemma ordinary_exact (R : Type u) [CommRing R] [Module.Injective R R]
    (M N P : ModuleCat.{u} R) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (he : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective g.dualMap ∧ Function.Exact g.dualMap f.dualMap ∧
      Function.Surjective f.dualMap := by
  refine ⟨LinearMap.dualMap_injective_of_surjective hg, ?_, ?_⟩
  · rw [LinearMap.exact_iff,
      LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective g hg,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range,
      LinearMap.exact_iff.mp he]
  · intro h
    obtain ⟨k, hk⟩ := Module.Injective.extension_property R R M N f hf h
    exact ⟨k, hk⟩


private lemma single_projective_terms (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] (i : ℤ) :
    Module.Projective R
        (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M).X i) ∧
      Module.Finite R (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M).X i) := by
  by_cases hi : i = 0
  · subst hi
    let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
    exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
      Module.Finite.equiv e.toLinearEquiv.symm⟩
  · have : Subsingleton
        (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    exact ⟨@Module.Projective.of_free R _ _ _ _
      (Module.Free.of_subsingleton R _), Module.Finite.of_finite⟩

private lemma perfect_single_pid (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (M : ModuleCat.{u} R) [Module.Finite R M] :
    DerivedCategory.IsPerfectRingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have : Module.Finite R (LinearMap.ker f) := Module.IsNoetherian.finite R _
  have : Module.Free R (LinearMap.ker f) := Module.free_of_finite_type_torsion_free'
  let S := f.shortComplexKer
  have hS := LinearMap.shortExact_shortComplexKer hf
  let S' := S.map (CochainComplex.singleFunctor (ModuleCat.{u} R) 0)
  have : PreservesFiniteLimits (CochainComplex.singleFunctor (ModuleCat.{u} R) 0) :=
    inferInstanceAs (PreservesFiniteLimits
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0))
  have : PreservesFiniteColimits (CochainComplex.singleFunctor (ModuleCat.{u} R) 0) :=
    inferInstanceAs (PreservesFiniteColimits
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0))
  have hS' : S'.ShortExact := hS.map_of_exact _
  have : S'.X₁.IsStrictlyGE 0 :=
    inferInstanceAs (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj S.X₁).IsStrictlyGE 0)
  have : S'.X₁.IsStrictlyLE 0 :=
    inferInstanceAs (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj S.X₁).IsStrictlyLE 0)
  have : S'.X₂.IsStrictlyGE 0 :=
    inferInstanceAs (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj S.X₂).IsStrictlyGE 0)
  have : S'.X₂.IsStrictlyLE 0 :=
    inferInstanceAs (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj S.X₂).IsStrictlyLE 0)
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have hcone := DerivedCategory.isPerfect_Q_obj_mappingCone S'.f 0 0 0 0
    (single_projective_terms R S.X₁) (single_projective_terms R S.X₂)
  have hperfect := hcone.of_iso
    (asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S')) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M).symm)
  exact hperfect

private lemma derived_dual_equivalence (R : Type u) [CommRing R]
    (hD : ∀ K, boundedFiniteCoefficientComplex R K →
      boundedFiniteCoefficientComplex R ((coefficientDerivedDual R).obj (op K)))
    (hδ : ∀ K, boundedFiniteCoefficientComplex R K →
      IsIso (coefficientDerivedEvaluation K)) :
    ∃ F : (boundedFiniteCoefficientComplex R).FullSubcategoryᵒᵖ ⥤
        (boundedFiniteCoefficientComplex R).FullSubcategory,
      F.IsEquivalence ∧
        Nonempty (F ⋙ (boundedFiniteCoefficientComplex R).ι ≅
          (boundedFiniteCoefficientComplex R).ι.op ⋙ coefficientDerivedDual R) := by
  let : BraidedCategory (DerivedCategory (ModuleCat.{u} R)) := coefficientBraided R
  let e := ObjectProperty.liftDualEquivalence (boundedFiniteCoefficientComplex R)
    (coefficientDerivedDual R) hD (MonoidalClosed.toIhomIhomNatTrans (𝟙_ _))
    (fun K hK ↦ by
      have := hδ K hK
      rwa [coefficient_eval_eq] at this)
  exact ⟨e.functor, inferInstance, ⟨Iso.refl _⟩⟩

private lemma field_frobenius (R : Type u) [Field R] :
    coefficientFrobeniusProperties R := by
  have : Module.Injective R R := Module.injective_of_isSemisimpleRing R R
  refine ⟨inferInstance, inferInstance, ordinary_exact R, ?_, ?_⟩
  · intro M hM
    have := hM
    exact ⟨inferInstance, Module.bijective_dual_eval R M⟩
  · have hp : ∀ K, boundedFiniteCoefficientComplex R K → DerivedCategory.IsPerfect K := by
      intro K hK
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
      exact (DerivedCategory.isPerfect_iff K).2 ⟨⟨a, b, ha, hb⟩, hK.2⟩
    apply derived_dual_equivalence R
    · intro K hK
      have hpK := hp K hK
      exact ⟨hpK.ihom_unit.bounded, hpK.ihom_unit.finite_homology⟩
    · intro K hK
      let : BraidedCategory (DerivedCategory (ModuleCat.{u} R)) := coefficientBraided R
      rw [coefficient_eval_eq]
      exact DerivedCategory.IsPerfect.isIso_toIhomIhomUnit
        (hp K hK)

/-- The three self-injective coefficient stages have exact ordinary duality,
finite-module evaluation isomorphisms, and a derived anti-equivalence on bounded
finite cohomology. Algebraic closure means the algebraic field, with ordinary duals.
Source: blueprint lem-weil-coefficient-frobenius, clause 1; Stacks 0AVF
(blueprint: lem-weil-coefficient-frobenius).

Proof:
1. The DVR description of O_E gives principal ideals, hence Noetherianity.
   Its positive quotients are finite; therefore Artinian and Noetherian. Fields
   are Artinian and Noetherian because their only ideals are zero and the unit ideal.
2. Every quotient ideal is (pi^i), 0 <= i <= n; cancellation in O_E gives
   Ann(pi^(n-i)) = (pi^i), including i = 0, n and n = 1.
3. A linear map (pi^i) -> A has value pi^i b at pi^i, and multiplication by b
   extends it. Apply lem-sf-baer-criterion. For a field use its two ideals.
   Restriction is onto for an inclusion, and its kernel is the maps factoring
   through the quotient: this proves exactness on all modules.
4. A finite A-module has finite underlying set, hence finite dual. Present it by
   two finite free modules using lem-sc-noetherian-finite-module-finite-presentation.
   Twice dualizing preserves the right-exact presentation. Finite free evaluation
   is invertible by lem-sf-finite-projective-dual, and naturality identifies the
   induced cokernel isomorphism with evaluation on M.
5. For either field stage a finite spanning list reduces to a finite basis.
   Apply lem-sf-finite-projective-dual; no finiteness of the underlying field is used.
6. The ring in degree zero is K-injective by self-injectivity and
   lem-weil-pbc-bounded-below-injectives-kinjective. Thus RHom(-,R) is computed by
   (DC)^j = Hom(C^(-j),R), with d(f) = (-1)^(j+1) f d_C.
   Exactness and lem-sp-exact-functor-preserves-homology give H^j(DC) = D H^(-j)(C).
   The signed evaluation x |-> (f |-> (-1)^j f(x)) is a chain map and a
   quasi-isomorphism by finite-module evaluation. Localization inverts it.
   It obeys D(delta_C) delta_DC = 1, so the restricted dual is its own
   contravariant quasi-inverse. Exactness on triangles follows from the cone
   formula, or lem-sf-exact-functor-derived-triangulated. -/
theorem coefficient_frobenius
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) :
    coefficientFrobeniusProperties (Padic.coefficientExtensionRing l E n) ∧
      coefficientFrobeniusProperties E ∧
      coefficientFrobeniusProperties (AlgebraicClosure (Padic l)) := by
  refine ⟨?_, field_frobenius E, field_frobenius (AlgebraicClosure (Padic l))⟩
  let R := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have hdata := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsDiscreteValuationRing R := hdata.2.2.2.2.2.2.2.1
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := hdata.2.2.2.2.1
  have hgen : Ideal.span ({π} : Set R) = Padic.coefficientExtensionMaximalIdeal l E :=
    hdata.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hπne : π ≠ 0 := by
    intro hzero
    have hne : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
      hdata.2.2.2.2.2.2.2.2.2.1
    apply hne
    rw [← hgen, hzero, Ideal.span_singleton_zero]
  have hπ : Irreducible π := Ideal.irreducible_of_isMaximal_span_singleton hπne
    (by rw [hgen]; exact hmax)
  change coefficientFrobeniusProperties (R ⧸ Ideal.span {π} ^ n)
  rw [Ideal.span_singleton_pow]
  let A := R ⧸ Ideal.span {π ^ n}
  have : Module.Injective A A := IsDiscreteValuationRing.injective_quotient_pow hπ n
  have : Finite A := by
    simpa only [Padic.coefficientExtensionRing, Padic.coefficientExtensionIdeal,
      Ideal.span_singleton_pow] using Padic.finite_coefficientExtensionRing l E n hn
  have : IsArtinianRing A := isArtinian_of_finite
  refine ⟨inferInstance, inferInstance, ordinary_exact A, ?_, ?_⟩
  · intro M hM
    have := hM
    have : Finite M := Module.finite_of_finite A
    have : Module.IsReflexive A M :=
      IsDiscreteValuationRing.isReflexive_quotient_pow hπ n M
    have : Finite (Module.Dual A M) := Finite.of_injective
      (fun f : Module.Dual A M ↦ (f : M → A)) DFunLike.coe_injective
    exact ⟨Module.Finite.of_finite, Module.bijective_dual_eval A M⟩
  · have : IsNoetherianRing A := isNoetherian_of_finite A A
    let I := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
    let e : DerivedCategory.Q.obj I ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)) :=
      DerivedCategory.unitIsoQObjUnitComplex.symm
    have hI : ∀ i : ℤ, Injective (I.X i) := by
      intro i
      by_cases hi : i = 0
      · subst hi
        exact Injective.of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).symm
          (Module.injective_object_of_injective_module A A)
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).injective
    have hperfect : DerivedCategory.IsPerfect (𝟙_ (DerivedCategory (ModuleCat.{u} A))) :=
      (DerivedCategory.isPerfect_Q_obj I 0 0
        (single_projective_terms A (ModuleCat.of A A))).of_iso e
    have hscalar : IsIso (MonoidalClosed.curry
        (ρ_ (𝟙_ (DerivedCategory (ModuleCat.{u} A)))).hom) := by
      exact scalar_unit_iso
    exact DerivedCategory.dualizingComplex_bounded_duality A _
      ⟨I, ⟨0, 0, fun i hi ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _
        (by omega)⟩, hI, ⟨e⟩⟩ hperfect.finite_homology hscalar

/-- Integral coefficients are not quasi-Frobenius; finite projectives, but not
all finite modules, are ordinarily reflexive.
Source: blueprint lem-weil-coefficient-frobenius, clause 2; Stacks 0AVF and 07VI
(blueprint: lem-weil-coefficient-frobenius).

Proof (node Step 7): T = O_E/(pi) is nonzero. Every map T -> O_E is zero,
since pi annihilates its image and O_E is a domain. Thus T** = 0 and its
ordinary evaluation is not invertible. Dualizing multiplication by pi leaves
a nonsurjective multiplication-by-pi map, contradicting self-injectivity
(lem-sf-baer-criterion). Finite projectives remain reflexive by
lem-sf-finite-projective-dual. -/
theorem integral_coefficient_ordinary_duality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    ¬ (IsArtinianRing (Padic.coefficientExtensionIntegers l E) ∧
      Module.Injective (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionIntegers l E)) ∧
    (∀ M : ModuleCat.{u} (Padic.coefficientExtensionIntegers l E),
      Module.Finite (Padic.coefficientExtensionIntegers l E) M →
      Module.Projective (Padic.coefficientExtensionIntegers l E) M →
      Function.Bijective (Module.Dual.eval (Padic.coefficientExtensionIntegers l E) M)) ∧
    ∃ M : ModuleCat.{u} (Padic.coefficientExtensionIntegers l E),
      Module.Finite (Padic.coefficientExtensionIntegers l E) M ∧
      ¬ Function.Bijective (Module.Dual.eval (Padic.coefficientExtensionIntegers l E) M) := by
  let R := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have hdata := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsDiscreteValuationRing R := hdata.2.2.2.2.2.2.2.1
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := hdata.2.2.2.2.1
  have hgen : Ideal.span ({π} : Set R) = Padic.coefficientExtensionMaximalIdeal l E :=
    hdata.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hπne : π ≠ 0 := by
    intro hzero
    have hne : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
      hdata.2.2.2.2.2.2.2.2.2.1
    apply hne
    rw [← hgen, hzero, Ideal.span_singleton_zero]
  have hπ : Irreducible π := Ideal.irreducible_of_isMaximal_span_singleton hπne
    (by rw [hgen]; exact hmax)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hArt, _⟩
    have : IsArtinianRing R := hArt
    exact hπ.not_isUnit (IsArtinianRing.isUnit_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero))
  · intro M hfinite hprojective
    have := hfinite
    have := hprojective
    exact Module.bijective_dual_eval R M
  · refine ⟨ModuleCat.of R (R ⧸ Ideal.span {π}), inferInstance, ?_⟩
    intro heval
    exact IsDiscreteValuationRing.not_isReflexive_quotient hπ ⟨heval⟩

/-- Every bounded integral complex with finite cohomology is perfect and its
canonical derived evaluation is invertible.
Source: blueprint lem-weil-coefficient-frobenius, clause 2; Stacks 066Z and 07VI
(blueprint: lem-weil-coefficient-frobenius).

Proof (node Steps 8--9): O_E is Noetherian by its principal-ideal DVR description.
For a finite module M choose a finite presentation O_E^u -> O_E^v -> M.
Its relation module is finite and torsion-free, hence finite free by
lem-sc-dvr-fg-torsionfree-free. This gives a length-one finite-free resolution.
Assemble the finitely many perfect cohomology objects using
lem-sf-perfect-cohomology-assembly. For the resulting bounded finite-projective
model apply the signed termwise evaluation calculation of Step 9, stated next. -/
theorem integral_coefficient_derived_duality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)))
    (hK : boundedFiniteCoefficientComplex (Padic.coefficientExtensionIntegers l E) K) :
    DerivedCategory.IsPerfectRingComplex K ∧ IsIso (coefficientDerivedEvaluation K) := by
  let R := Padic.coefficientExtensionIntegers l E
  have hdata := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsDiscreteValuationRing R := hdata.2.2.2.2.2.2.2.1
  have hperfect : DerivedCategory.IsPerfectRingComplex K := by
    apply DerivedCategory.isPerfectRingComplex_of_perfect_cohomology K
    · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
      have : K.IsGE a := ha
      have : K.IsLE b := hb
      refine ⟨a, b, fun i hi ↦ ?_⟩
      rcases hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE K a i hi
      · exact DerivedCategory.isZero_of_isLE K b i hi
    · intro i
      have := hK.2 i
      exact perfect_single_pid R _
  refine ⟨hperfect, ?_⟩
  let : BraidedCategory (DerivedCategory (ModuleCat.{u} R)) :=
    coefficientBraided R
  rw [coefficient_eval_eq]
  exact DerivedCategory.IsPerfect.isIso_toIhomIhomUnit hperfect

/-- Perfect complexes over any commutative ring have canonical derived biduality;
no self-injectivity is assumed.
Source: blueprint lem-weil-coefficient-frobenius, clause 3; Stacks 07VI and 0A66
(blueprint: lem-weil-coefficient-frobenius).

Proof (node Step 9): Choose a bounded finite-projective model P. It is
K-projective by lem-sc-bounded-above-projective-kprojective. For a K-injective
resolution R[0] -> I the cone of Hom(P,R[0]) -> Hom(P,I) is the Hom complex
into the acyclic cone, hence acyclic. Thus termwise duality computes RHom.
The dual DP is again bounded finite projective by lem-sf-finite-projective-dual,
so the same calculation computes the double dual by DDP. In degree j,
x |-> (f |-> (-1)^j f(x)) commutes with differentials and is an isomorphism
by finite-projective evaluation. This chain isomorphism represents precisely
the transpose of the Koszul-interchanged evaluation used in the definition. -/
theorem perfect_coefficient_derived_evaluation
    (R : Type u) [CommRing R] (K : DerivedCategory (ModuleCat.{u} R))
    (hK : DerivedCategory.IsPerfectRingComplex K) :
    IsIso (coefficientDerivedEvaluation K) := by
  let : BraidedCategory (DerivedCategory (ModuleCat.{u} R)) :=
    coefficientBraided R
  rw [coefficient_eval_eq]
  exact DerivedCategory.IsPerfect.isIso_toIhomIhomUnit hK

/-- The finite-Tor point consequence at the finite coefficient stage.
At the two field stages all bounded finite-cohomology complexes have finite Tor
amplitude; at the integral stage the preceding integral theorem applies already.
Source: blueprint lem-weil-coefficient-frobenius, final clause; Stacks 07VI
(blueprint: lem-weil-coefficient-frobenius).

Proof (node Step 10): lem-trf-finite-tor-amplitude-perfect supplies a bounded
finite-free model for the finite-stage complex of finite Tor amplitude.
Apply perfect_coefficient_derived_evaluation; it has no injectivity hypothesis.
Over fields finite cohomology is finite free, and
lem-sf-perfect-cohomology-assembly gives perfectness. Over O_E use Step 8. -/
theorem finiteTor_point_coefficient_evaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (K : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionRing l E n)))
    (hK : boundedFiniteCoefficientComplex (Padic.coefficientExtensionRing l E n) K)
    (hTor : DerivedCategory.finiteTorAmplitude
      (ModuleCat.{u} (Padic.coefficientExtensionRing l E n)) K) :
    IsIso (coefficientDerivedEvaluation K) := by
  let R := Padic.coefficientExtensionRing l E n
  let : Finite R := Padic.finite_coefficientExtensionRing l E n hn
  let : IsNoetherianRing R := isNoetherian_of_finite R R
  have hfinite : ∀ i : ℤ,
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) :=
    hK.2
  have hperfect : DerivedCategory.IsPerfect K :=
    DerivedCategory.isPerfect_of_finiteTorAmplitude hK.1 hfinite hTor
  have hperfect' : DerivedCategory.IsPerfectRingComplex K := by
    obtain ⟨P, a, b, ha, hb, hP, e⟩ := hperfect
    exact ⟨P, a, b, ha, hb, hP, e⟩
  exact perfect_coefficient_derived_evaluation R K hperfect'

end WeilConjectures
