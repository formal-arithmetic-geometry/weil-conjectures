/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Sheaf.RingTheory.ContractedPrimeTensorComparison
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Fixed tensor kernel and stalk criterion

Source: Stacks Project, Algebra, Tag 05CL, lemma-universally-injective-check-stalks
(blueprint: lem-trf-fixed-tensor-kernel-stalk-criterion).

The proposition abbreviations expand the actual localized tensor maps with canonical
scalar structures, following the interface of the contracted-prime comparison dependency.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace LocalizedModule

/-- Injectivity of the actual fixed tensor test at a contracted prime, with the canonical
restriction of scalars along `Localization.localRingHom`.
Source: Stacks Project, Algebra, Tag 05CL, displayed tensor identities
(blueprint: lem-trf-fixed-tensor-kernel-stalk-criterion). -/
noncomputable abbrev ContractedPrimeTensorTestInjective
    (R : Type u) (A : Type v) (M : Type w) (M' : Type x) (N : Type y)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
    [Module A M] [Module A M'] [Module R M] [Module R M'] [Module R N]
    [IsScalarTower R A M] [IsScalarTower R A M']
    (f : M →ₗ[A] M') (q : PrimeSpectrum A) : Prop :=
  letI := (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
    q.asIdeal (algebraMap R A) rfl).toAlgebra
  letI : Module (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
      (LocalizedModule q.asIdeal.primeCompl M) :=
    Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
      q.asIdeal (algebraMap R A) rfl)
  letI : Module (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
      (LocalizedModule q.asIdeal.primeCompl M') :=
    Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
      q.asIdeal (algebraMap R A) rfl)
  letI := IsScalarTower.of_compHom
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M)
  letI := IsScalarTower.of_compHom
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M')
  let tq := TensorProduct.AlgebraTensorModule.rTensor
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (LocalizedModule (q.asIdeal.comap (algebraMap R A)).primeCompl N)
    (LocalizedModule.map q.asIdeal.primeCompl f)
  Function.Injective tq

/-- The normalized kernel isomorphism for the fixed tensor test. The comparison `c` is
extracted from the recorded dependency, whose pure-fraction formulas uniquely determine it.
The displayed equation specifies the map induced by localizing the kernel inclusion.
Source: Stacks Project, Algebra, Tag 05CL, localized kernel argument
(blueprint: lem-trf-fixed-tensor-kernel-stalk-criterion). -/
noncomputable abbrev ContractedPrimeTensorKernelComparison
    (R : Type u) (A : Type v) (M : Type w) (M' : Type x) (N : Type y)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
    [Module A M] [Module A M'] [Module R M] [Module R M'] [Module R N]
    [IsScalarTower R A M] [IsScalarTower R A M']
    (f : M →ₗ[A] M') (q : PrimeSpectrum A) : Prop :=
  letI := (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
    q.asIdeal (algebraMap R A) rfl).toAlgebra
  letI : Module (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
      (LocalizedModule q.asIdeal.primeCompl M) :=
    Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
      q.asIdeal (algebraMap R A) rfl)
  letI : Module (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
      (LocalizedModule q.asIdeal.primeCompl M') :=
    Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
      q.asIdeal (algebraMap R A) rfl)
  letI := IsScalarTower.of_compHom
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M)
  letI := IsScalarTower.of_compHom
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M')
  let tq := TensorProduct.AlgebraTensorModule.rTensor
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (LocalizedModule (q.asIdeal.comap (algebraMap R A)).primeCompl N)
    (LocalizedModule.map q.asIdeal.primeCompl f)
  let T := TensorProduct.AlgebraTensorModule.rTensor R N f
  let α := Classical.choose (contractedPrime_tensor_comparison R A M M' N q)
  let β := Classical.choose
    (Classical.choose_spec (contractedPrime_tensor_comparison R A M M' N q))
  ∃ e : LocalizedModule q.asIdeal.primeCompl T.ker ≃ₗ[Localization.AtPrime q.asIdeal]
      tq.ker,
    ∀ z : LocalizedModule q.asIdeal.primeCompl T.ker,
      (e z).val = β (α (LocalizedModule.map q.asIdeal.primeCompl T.ker.subtype z))

/-- The kernel of a fixed tensor test localizes to the kernel of its contracted-prime test,
by exactly the localized inclusion followed by the canonical tensor comparison. Injectivity
is detected by all primes, and equivalently by all maximal ideals, without flatness or
finiteness assumptions.
Source: Stacks Project, Algebra, Tag 05CL, lemma-universally-injective-check-stalks
(blueprint: lem-trf-fixed-tensor-kernel-stalk-criterion).

Proof:
1. Put X = M tensor_R N, Y = M' tensor_R N, T = f tensor 1, and K = ker T.
   Apply `lem-weil-pbc-localization-module-exact` over A to K → X → Y. The localized
   inclusion has image ker T_q and is injective: if k/s maps to zero, a denominator t
   kills its numerator in X, hence also in K. Thus K_q identifies with ker T_q.
2. The naturality equation of `lem-trf-contracted-prime-tensor-comparison` identifies
   ker T_q with ker tq via c = β ∘ α. The inverse is the restriction of c⁻¹: if tq(y)=0,
   naturality and injectivity of the target comparison show T_q(c⁻¹(y))=0.
   Compose with step 1; its underlying map is c after the localized inclusion.
3. If T is injective, K = 0, hence K_q = 0. Step 2 gives injectivity of every tq,
   including at maximal ideals, which are prime.
4. Conversely, if every maximal test is injective, K_m = 0. A nonzero k in K has
   proper annihilator I. By `lem-weil-pbc-proper-ideal-contained-in-maximal`, some
   maximal m contains I. The equality k/1 = 0 gives s outside m with sk = 0, a
   contradiction to s in I. Thus K = 0. Prime tests imply maximal tests as well. -/
theorem fixedTensor_kernel_stalk_criterion
    (R : Type u) (A : Type v) (M : Type w) (M' : Type x) (N : Type y)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
    [Module A M] [Module A M'] [Module R M] [Module R M'] [Module R N]
    [IsScalarTower R A M] [IsScalarTower R A M']
    (f : M →ₗ[A] M') :
    (∀ q : PrimeSpectrum A, ContractedPrimeTensorKernelComparison R A M M' N f q) ∧
    (Function.Injective (TensorProduct.AlgebraTensorModule.rTensor R N f) ↔
      ∀ q : PrimeSpectrum A, ContractedPrimeTensorTestInjective R A M M' N f q) ∧
    (Function.Injective (TensorProduct.AlgebraTensorModule.rTensor R N f) ↔
      ∀ q : PrimeSpectrum A, q.asIdeal.IsMaximal →
        ContractedPrimeTensorTestInjective R A M M' N f q) := by
  sorry

end LocalizedModule
