/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.IntegralHeartLocalModel
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Paper.IntegralHeartRealizationExact
import Sheaf.Paper.IntegralHeartLocalDualityDescent
import Sheaf.Paper.IntegralHeartResidueDual

/-!
# Duals of integral constructible sheaves on a stratum

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-integral-heart,
`sk-lem-int-integral-heart-dualizable.md`; Stacks Project, Tags 08JJ and 0FPU
(blueprint: det-lem-int-integral-heart-dualizable).

The coefficient ring and scalar realization are exactly those of IntegralHeartLocalModel.
In particular, coefficients are continuous completed coefficients, not the constant DVR.
The small presentation of the finite extension keeps its universe independent of the site.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

private theorem shortExact_dualizable_tor {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [HasDerivedCategory.{v} A]
    [Abelian.HasFunctorialFlatResolution A]
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : IsDualizable S.X₁) (h₂ : IsDualizable S.X₂) :
    IsDualizable ((DerivedCategory.singleFunctor A 0).obj S.X₃) ∧
    DerivedCategory.torAmplitudeIn A (-1) 0
      ((DerivedCategory.singleFunctor A 0).obj S.X₃) := by
  refine ⟨DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hS h₁ h₂, ?_⟩
  let S' := S.map (HomologicalComplex.single A (.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have : (CochainComplex.mappingCone S'.f).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  have : (CochainComplex.mappingCone S'.f).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  let e := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S')) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app S.X₃).symm
  exact (DerivedCategory.torAmplitudeIn A (-1) 0).prop_of_iso e
    (DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ (-1) 0
      (fun n ↦ (DerivedCategory.isDualizable_mappingCone_single_X h₁ h₂ S'.f n).flat))

private theorem finite_free_presentation {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (a b : ℕ) (f : (Fin a → R) →ₗ[R] (Fin b → R))
      (g : (Fin b → R) →ₗ[R] M),
      Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g := by
  classical
  obtain ⟨b, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let g : (Fin b → R) →ₗ[R] M :=
    (Finsupp.linearCombination R s).comp
      (Finsupp.linearEquivFunOnFinite R R (Fin b)).symm.toLinearMap
  have hg : Function.Surjective g := by
    apply LinearMap.range_eq_top.mp
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    exact (Finsupp.range_linearCombination R).trans hs
  let L := LinearMap.ker g
  let : Module.Finite R L := inferInstance
  obtain ⟨a, basis⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := L)
  let e : L ≃ₗ[R] (Fin a → R) := basis.equivFun
  let f : (Fin a → R) →ₗ[R] (Fin b → R) := L.subtype.comp e.symm.toLinearMap
  refine ⟨a, b, f, g, ?_, ?_, hg⟩
  · exact L.subtype_injective.comp e.symm.injective
  · intro x
    constructor
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [f]⟩
    · rintro ⟨y, rfl⟩
      exact (e.symm y).property

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- Restrict the sheaf to a stratum and place it in degree zero. This is only an
abbreviation for the recorded inverse image and single-complex functors.
Source: blueprint integral-heart-dualizable, notation C restricted to S
(blueprint: det-lem-int-integral-heart-dualizable). -/
abbrev integralHeartStratumComplex {X S : Scheme.{u}} (f : S ⟶ X)
    (C : SmallAdicCompletion.Modules ℓ E X) : integralHeartDerivedCategory.{u} ℓ E S :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E) f).obj C)

/-- Local duality, the two Tor bounds, and the residue-sheaf example. The module N is
chosen separately on each chart; no freeness or torsion-freeness of N is assumed.
`ExactPairing K D` includes evaluation D tensor K to the unit, coevaluation from the
unit to K tensor D, and both triangle identities. The displayed dual is the recorded
relative derived internal Hom into the completed coefficient unit.

Source: blueprint main-20261015, integral-heart-dualizable; Stacks 08JJ and 0FPU
(blueprint: det-lem-int-integral-heart-dualizable).

Proof: on each chart separately, finite generation over the coefficient DVR gives a
surjection from a finite free module. Its kernel is finitely generated and torsion-free,
hence finite free. Exact completed scalar realization sends this presentation to a
short exact sequence with dualizable first two terms. The generic derived short-exact
criterion gives dualizability of its degree-zero quotient. Its two-term mapping-cone
model has flat terms and support [-1,0], which gives that Tor bound against every
module sheaf. Transfer these assertions along the given local-model isomorphisms.
Cover descent gives the global canonical tensor--Hom comparison and the global Tor
bound. The closed-monoidal duality criterion constructs its exact pairing, including
both triangle identities, with the displayed internal Hom into the completed unit.
Duality reverses the Tor interval to [0,1]. Finally, the residue module has the short
exact uniformizer resolution by two copies of the unit. Dualizing its distinguished
triangle identifies its dual with the residue module shifted by -1, in degree one. -/
theorem integralHeartDualizable
    (X : Scheme.{u}) (C : SmallAdicCompletion.Modules ℓ E X)
    (_hC : IsConstantModelConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X C)
    (s : Scheme.Stratification X) (a : Fin s.n)
    (_hmodel : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
      ∀ i : 𝒰.I₀,
        ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
          Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
          Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
              (𝒰.f i ≫ s.immersion a)).obj C ≅
            (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)) :
    Nonempty (ExactPairing (integralHeartStratumComplex ℓ E (s.immersion a) C)
      (((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (s.domain a)).obj (op (integralHeartStratumComplex ℓ E (s.immersion a) C))).obj
          (𝟙_ (integralHeartDerivedCategory.{u} ℓ E (s.domain a))))) ∧
    DerivedCategory.torAmplitudeIn _ (-1) 0
      (integralHeartStratumComplex ℓ E (s.immersion a) C) ∧
    DerivedCategory.torAmplitudeIn _ 0 1
      (((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (s.domain a)).obj (op (integralHeartStratumComplex ℓ E (s.immersion a) C))).obj
          (𝟙_ (integralHeartDerivedCategory.{u} ℓ E (s.domain a)))) ∧
    Nonempty
      ((((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
          (s.domain a)).obj (op ((DerivedCategory.singleFunctor _ 0).obj
            (SmallAdicCompletion.finiteModule ℓ E (s.domain a) 0)))).obj
              (𝟙_ (integralHeartDerivedCategory.{u} ℓ E (s.domain a)))) ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          (SmallAdicCompletion.finiteModule ℓ E (s.domain a) 0))⟦(-1 : ℤ)⟧) := by
  classical
  let A := integralHeartScalars.{u} ℓ E
  have hDvr : IsDiscreteValuationRing
      (SmallAdicCompletion.Coefficients.integers ℓ E) := by
    exact (Padic.extension_integers_dvr ℓ
      (SmallAdicCompletion.Coefficients.field ℓ E)
      (Padic.coefficientExtensionAbsoluteValue ℓ _)
      (spectralNorm_extends (K := Padic ℓ)
        (L := SmallAdicCompletion.Coefficients.field ℓ E))).choose_spec.choose_spec.2.2.2.2.2.2.2.1
  let : IsDomain (SmallAdicCompletion.Coefficients.integers ℓ E) := inferInstance
  let : IsDiscreteValuationRing
      (SmallAdicCompletion.Coefficients.integers ℓ E) := hDvr
  let : IsPrincipalIdealRing (SmallAdicCompletion.Coefficients.integers ℓ E) :=
    IsDiscreteValuationRing.toIsPrincipalIdealRing
  let : IsDomain A := by
    apply MulEquiv.isDomain (SmallAdicCompletion.Coefficients.integers ℓ E)
    exact (ULift.ringEquiv (R := SmallAdicCompletion.Coefficients.integers ℓ E)).toMulEquiv
  let e := (ULift.ringEquiv (R := SmallAdicCompletion.Coefficients.integers ℓ E))
  let : IsPrincipalIdealRing A :=
    ⟨(isPrincipalIdealRing_iff _).1 (.of_surjective _ e.symm.surjective)⟩
  obtain ⟨𝒰, h𝒰⟩ := _hmodel
  have hlocal (i : 𝒰.I₀) :
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
          (𝒰.f i)).obj
          ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
            (s.immersion a)).obj C))) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0 ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
          (𝒰.f i)).obj
          ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
            (s.immersion a)).obj C))) := by
    obtain ⟨N, hN, ⟨eN⟩⟩ := h𝒰 i
    let := hN
    obtain ⟨r, t, f, g, hf, hfg, hg⟩ := finite_free_presentation (R := A) N
    let f' : ModuleCat.of A (Fin r → A) ⟶ ModuleCat.of A (Fin t → A) := ModuleCat.ofHom f
    let g' : ModuleCat.of A (Fin t → A) ⟶ N := ModuleCat.ofHom g
    have hw : f' ≫ g' = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (hfg (f x)).2 ⟨x, rfl⟩
    let T := ShortComplex.mk f' g' hw
    have hT : T.ShortExact :=
      { mono_f := (ModuleCat.mono_iff_injective f').2 hf
        epi_g := (ModuleCat.epi_iff_surjective g').2 hg
        exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).2 hfg }
    let F := integralHeartRealization.{u} ℓ E (𝒰.X i)
    obtain ⟨hFlim, hFcolim, hFfree⟩ := integralHeartRealization_exact_free ℓ E (𝒰.X i)
    let := hFlim
    let := hFcolim
    have h := shortExact_dualizable_tor (hT.map_of_exact F) (hFfree r) (hFfree t)
    let e := (DerivedCategory.singleFunctor _ 0).mapIso
      (((CondensedRing.upperStarComp
        (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (𝒰.f i) (s.immersion a)).app C).symm ≪≫ eN)
    exact ⟨h.1.of_iso e.symm,
      (DerivedCategory.torAmplitudeIn _ (-1) 0).prop_of_iso e.symm h.2⟩
  obtain ⟨hc, hK⟩ := integralHeart_local_duality_descent
    (SmallAdicCompletion.Coefficients.integerRing ℓ E) (s.domain a)
    ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
      (s.immersion a)).obj C) 𝒰 (-1) 0 hlocal
  let := hc
  let K := integralHeartStratumComplex ℓ E (s.immersion a) C
  let := MonoidalClosed.exactPairingOfIsIso K
  obtain ⟨b⟩ := DerivedCategory.nonempty_braidedCategory
    (SmallAdicCompletion.Modules ℓ E (s.domain a))
  let := b
  let := BraidedCategory.exactPairing_swap ((ihom K).obj (𝟙_ _)) K
  have hpair : ExactPairing K ((ihom K).obj (𝟙_ _)) := inferInstance
  have hdualIH : DerivedCategory.torAmplitudeIn _ 0 1 ((ihom K).obj (𝟙_ _)) := by
    exact DerivedCategory.torAmplitudeIn_of_exactPairing hK
  have hdual : DerivedCategory.torAmplitudeIn _ 0 1
      (((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
        (s.domain a)).obj (op K)).obj (𝟙_ _)) := by
    change DerivedCategory.torAmplitudeIn _ 0 1 ((ihom K).obj (𝟙_ _))
    exact hdualIH
  refine ⟨?_, hK, hdual, integralHeart_residue_dual ℓ E (s.domain a)⟩
  change Nonempty (ExactPairing K ((ihom K).obj (𝟙_ _)))
  exact ⟨hpair⟩

end AlgebraicGeometry.ProEtale
