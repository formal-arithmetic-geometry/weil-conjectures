/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceData
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularScalarInjectiveDivisibility
import WeilConjectures.CategoryTheory.SixFunctors.QuotientAdjunctionKernel
import all WeilConjectures.AlgebraicGeometry.Adic.AdicReductionTriangle
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralScalarRegular

/-! # The actual ordinary quotient kernel and injective divisibility

Source: Stacks Tags 03D7, 06YP and 079P; the normalized right-exact tensor sequence and evaluation
of the ordinary coinduction adjunction.
(blueprint: lem-sf-regular-quotient-injective-kernel). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale SheafOfModules SheafOfModules.RegularQuotientCone
namespace WeilConjectures

attribute [-instance] PrincipalKoszulStrictReplacement.siteSmall
  PrincipalKoszulStrictReplacement.abSheafify PrincipalKoszulStrictReplacement.abLocallyBijective
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived
  GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard

private local instance (T : Scheme.{u}) : EssentiallySmall.{u+1} T.ProEt :=
  essentiallySmallSelf.{0,u,u+1} _
private local instance (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u,u} T
private local instance (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u,u} T
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)

/-- Quotient restriction is annihilated by the positive uniformizer scalar.
Source: Stacks Tags 03D7, 06YP and 079P; the normalized right-exact tensor sequence and
evaluation of the ordinary coinduction adjunction.
(blueprint: lem-sf-regular-quotient-injective-kernel). -/
theorem reductionScalar_restriction (N : scalarReductionTarget l E T n) :
    (scalar (completedIntegralCommRingSheafUnrestricted l E T)
      (reductionScalarSection l E T n)).app
        ((scalarReductionRestriction l E T n).obj N) = 0 := by
  ext U x
  have h := congrArg (fun f ↦ f.val.app U
    (1 : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U))
      (reductionScalar_zero l E T n)
  let a : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U :=
    (reductionScalarSection l E T n).val U
  change (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U
    (a * 1) * 1 = 0 at h
  simp only [mul_one] at h
  change (completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U
    a • (@id (N.val.obj U) x) = 0
  rw [h, zero_smul]

/-- Ordinary coinduction, after restriction, is the scalar kernel via its actual counit.
Source: Stacks Tags 03D7, 06YP and 079P; the normalized right-exact tensor sequence and
evaluation of the ordinary coinduction adjunction.
(blueprint: lem-sf-regular-quotient-injective-kernel). -/
theorem scalarReductionCoinduction_kernel (I : scalarReductionSource l E T) :
    ∃ h : (scalarReductionCoinductionAdjunction l E T n).counit.app I ≫
        (scalar (completedIntegralCommRingSheafUnrestricted l E T)
          (reductionScalarSection l E T n)).app I = 0,
      Nonempty (IsLimit (KernelFork.ofι
        ((scalarReductionCoinductionAdjunction l E T n).counit.app I) h)) := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let φ := completedIntegralCommRingProjectionUnrestricted l E T n
  let t := reductionScalarSection l E T n
  let f := (scalar R t).app (unit (completedIntegralCoefficientSheafUnrestricted l E T))
  let p := ringMap φ
  let α := ReductionTensor.multiplicationNatural T R f
  have he : α = scalar R t := by
    ext M U x
    change (ReductionTensor.tensorMultiplication T R f M).val.app U x = _
    rw [ReductionTensor.tensorMultiplication_apply]
    let a : R.obj.obj U := t.val U
    change (a * 1) • x = a • x
    rw [mul_one]
  have hquot (M : scalarReductionSource l E T) :=
    ReductionTensor.tensor_complex_exact T R φ p f
      (reductionScalar_zero l E T n) (reductionScalar_shortExact l E T n)
      (by intro U; change (φ.hom.app U).hom 1 * 1 = 1; rw [map_one, mul_one]) M
  have hz (M : scalarReductionSource l E T) :
      (scalar R t).app M ≫ (pbcScalarAdjunction φ).unit.app M = 0 := by
    rw [← he]
    exact (hquot M).choose
  have hc (M : scalarReductionSource l E T) :
      IsColimit (CokernelCofork.ofπ ((pbcScalarAdjunction φ).unit.app M) (hz M)) := by
    have hs := (hquot M).choose_spec.1
    change (ShortComplex.mk ((α.app M)) _ _).Exact ∧ _ at hs
    simp only [he] at hs
    exact (((ShortComplex.mk _ _ (hz M)).exact_and_epi_g_iff_g_is_cokernel).mp hs).some
  exact quotientAdjunctionKernel (pbcScalarAdjunction φ)
    (scalarReductionCoinductionAdjunction l E T n) (scalar R t)
    (reductionScalar_restriction l E T n) hz hc I

/-- A regular positive uniformizer power is surjective on each section module of an
injective completed-coefficient sheaf.
Source: Stacks Tags 03D7, 06YP and 079P; the normalized right-exact tensor sequence and
evaluation of the ordinary coinduction adjunction.
(blueprint: lem-sf-regular-quotient-injective-kernel). -/
theorem reductionScalar_injective_surjective
    (I : scalarReductionSource l E T) [Injective I] (U : T.ProEtᵒᵖ) :
    Function.Surjective (fun x : I.val.obj U ↦
      (@id ((completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
        ((reductionScalarSection l E T n).val U)) • x) := by
  apply regularScalar_injective_surjective.{u+1,u}
    (completedIntegralCommRingSheafUnrestricted l E T) (reductionScalarSection l E T n)
  intro V
  let μ := (scalar (completedIntegralCommRingSheafUnrestricted l E T)
    (reductionScalarSection l E T n)).app
      (unit (completedIntegralCoefficientSheafUnrestricted l E T))
  have : Mono μ := (reductionScalar_shortExact l E T n).mono_f
  have : Mono ((SheafOfModules.evaluation
    (completedIntegralCoefficientSheafUnrestricted l E T) V).map μ) := inferInstance
  exact (ModuleCat.mono_iff_injective
    ((SheafOfModules.evaluation
      (completedIntegralCoefficientSheafUnrestricted l E T) V).map μ)).mp inferInstance

/-- On injective coefficients the ordinary coinduction counit is the first map of
an actual short exact sequence. Source: Stacks Tags 03D7, 06YP and 079P.
The kernel universal property gives exactness and a monomorphism; regular-scalar
divisibility on sections gives an epimorphism for the second map.
(blueprint: lem-sf-regular-quotient-injective-kernel). -/
theorem scalarReductionCoinduction_shortExact
    (I : scalarReductionSource l E T) [Injective I] :
    ∃ h : (scalarReductionCoinductionAdjunction l E T n).counit.app I ≫
        (scalar (completedIntegralCommRingSheafUnrestricted l E T)
          (reductionScalarSection l E T n)).app I = 0,
      (ShortComplex.mk ((scalarReductionCoinductionAdjunction l E T n).counit.app I)
        ((scalar (completedIntegralCommRingSheafUnrestricted l E T)
          (reductionScalarSection l E T n)).app I) h).ShortExact := by
  obtain ⟨h, ⟨hk⟩⟩ := scalarReductionCoinduction_kernel l E T n I
  let μ := (scalar (completedIntegralCommRingSheafUnrestricted l E T)
    (reductionScalarSection l E T n)).app I
  have : Epi μ.val := PresheafOfModules.epi_of_surjective
    (fun {U} ↦ reductionScalar_injective_surjective l E T n I U)
  have : Epi μ := (SheafOfModules.forget _).epi_of_epi_map
    (show Epi μ.val from inferInstance)
  have hm := (ShortComplex.mk
    ((scalarReductionCoinductionAdjunction l E T n).counit.app I) μ h
      ).exact_and_mono_f_iff_f_is_kernel.mpr ⟨hk⟩
  exact ⟨h, { exact := hm.1, mono_f := hm.2, epi_g := inferInstance }⟩

/-- The ordinary coinduction counit applied termwise, before any derived comparison.
Source: Stacks Tags 03D7 and 079P; termwise evaluation of the adjunction counit.
(blueprint: lem-sf-regular-quotient-injective-kernel). -/
def scalarReductionCoinductionCounitComplex
    (I : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ) :
    ((scalarReductionRestriction.{u, u} l E T n).mapHomologicalComplex (.up ℤ)).obj
        (((scalarReductionCoinduction l E T n).mapHomologicalComplex (.up ℤ)).obj I) ⟶ I where
  f i := (scalarReductionCoinductionAdjunction l E T n).counit.app (I.X i)
  comm' i j _ :=
    ((scalarReductionCoinductionAdjunction l E T n).counit.naturality (I.d i j)).symm

/-- On a complex of injective terms, the ordinary counit and scalar give a short exact
sequence of complexes. Source: Stacks Tags 03D7, 06YP and 079P.
Proof: apply the proved injective-module short exact sequence in each degree; evaluation
jointly detects exactness, monomorphisms and epimorphisms in the complex category.
(blueprint: lem-sf-regular-quotient-injective-kernel). -/
theorem scalarReductionCoinduction_complex_shortExact
    (I : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    [∀ i : ℤ, Injective (I.X i)] :
    ∃ h : scalarReductionCoinductionCounitComplex l E T n I ≫
        (complexScalar (completedIntegralCommRingSheafUnrestricted l E T)
          (reductionScalarSection l E T n)).app I = 0,
      (ShortComplex.mk (scalarReductionCoinductionCounitComplex l E T n I)
        ((complexScalar (completedIntegralCommRingSheafUnrestricted l E T)
          (reductionScalarSection l E T n)).app I) h).ShortExact := by
  have hz : scalarReductionCoinductionCounitComplex l E T n I ≫
      (complexScalar (completedIntegralCommRingSheafUnrestricted l E T)
        (reductionScalarSection l E T n)).app I = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (scalarReductionCoinduction_shortExact l E T n (I.X i)).choose
  refine ⟨hz, HomologicalComplex.shortExact_of_degreewise_shortExact _ ?_⟩
  intro i
  exact (scalarReductionCoinduction_shortExact l E T n (I.X i)).choose_spec

end WeilConjectures
