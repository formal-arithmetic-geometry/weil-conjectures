/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Universal injectivity checked at primes of the source algebra

Source: Stacks Project, Algebra, Tag 05CL, `lemma-universally-injective-check-stalks`,
conditions (1) and (4) (blueprint: lem-trf-universal-injective-check-stalks).

## Main declarations

* `LinearMap.localizedAtContractedPrime`: the canonical localized map over the contracted prime.
* `LinearMap.universally_injective_iff_localizedAtContractedPrime`: the stalk criterion.
-/

@[expose] public section

universe u v w x y

namespace LinearMap

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
variable [Module A M] [Module A N]

/-- The map on `q`-localizations, restricted along the canonical map `R_p → A_q`,
where `p = q ∩ R`. Source: Stacks Project, Algebra, Tag 05CL, condition (4)
(blueprint: lem-trf-universal-injective-check-stalks).
The underlying function is `m/s ↦ f(m)/s`; both scalar structures are restriction
along `Localization.localRingHom`, rather than chosen module structures. -/
noncomputable def localizedAtContractedPrime (f : M →ₗ[A] N) (q : PrimeSpectrum A) :
    @LinearMap (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
      (Localization.AtPrime (q.asIdeal.comap (algebraMap R A))) _ _ (RingHom.id _)
      (LocalizedModule q.asIdeal.primeCompl M) (LocalizedModule q.asIdeal.primeCompl N)
      _ _
      (Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
        q.asIdeal (algebraMap R A) rfl))
      (Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
        q.asIdeal (algebraMap R A) rfl)) :=
  letI := (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
    q.asIdeal (algebraMap R A) rfl).toAlgebra
  letI := Module.compHom (LocalizedModule q.asIdeal.primeCompl M)
    (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
      q.asIdeal (algebraMap R A) rfl)
  letI := Module.compHom (LocalizedModule q.asIdeal.primeCompl N)
    (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
      q.asIdeal (algebraMap R A) rfl)
  letI := IsScalarTower.of_compHom
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M)
  letI := IsScalarTower.of_compHom
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))
    (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl N)
  (LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))

/-- Universal injectivity over `R` is equivalent to universal injectivity of every `f_q`
over `R_p`, with `p = q ∩ R`. Source: Stacks Project, Algebra, Tag 05CL, conditions (1)
and (4) (blueprint: lem-trf-universal-injective-check-stalks).

Proof:
1. For any R-module L and prime q of A, put p = q ∩ R. Elements outside p act
   invertibly on M_q and N_q, giving their canonical R_p-actions. The localization-tensor
   comparison `lem-weil-pbc-localization-tensor-over-base` identifies
   (M tensor_R L)_q with M_q tensor_R L, by (m tensor l)/s ↦ (m/s) tensor l.
   Apply `lem-weil-pbc-localization-tensor-product` to the identity localization of M_q
   at R minus p and to L → L_p. The resulting map M_q tensor_R L → M_q tensor_{R_p} L_p
   is a localization; it is bijective since every denominator already acts invertibly
   on M_q tensor_R L. Do the same for N. These identifications commute with f, as
   their formulas on pure tensors show. If L is already an R_p-module, L → L_p is
   bijective by the fraction and zero criteria of `def-weil-pbc-module-localization`.
   Tensor symmetry gives the same comparisons for the left tensor maps used here.
2. Suppose every f_q is universally injective over R_p. For an R-module L, take
   K = ker(1_L tensor f), an A-submodule of L tensor_R M. At every maximal ideal m
   of A, exact localization (`lem-weil-pbc-localization-module-exact`) identifies K_m
   with the kernel of the localized tensor map. Step 1 and the assumption applied to
   L_p make this map injective. Hence K_m = 0. Apply
   `lem-weil-pbc-linear-map-bijective-at-maximal-localizations` to K → 0, whose maximal
   localizations are bijective, to get K = 0. Thus every left tensor map is injective.
3. Conversely suppose f is universally injective over R. Fix q and any R_p-module L,
   restricted to R. The map 1_L tensor_R f is injective; exact localization preserves
   its injectivity. Step 1 and L_p = L identify this localization with
   1_L tensor_{R_p} f_q. It is therefore injective for every L, as required. -/
theorem universally_injective_iff_localizedAtContractedPrime
    [Module R M] [Module R N] [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M →ₗ[A] N) :
    (∀ (L : Type (max u v w x y)) [AddCommGroup L] [Module R L],
      Function.Injective ((f.restrictScalars R).lTensor L)) ↔
    ∀ (q : PrimeSpectrum A) (L : Type (max u v w x y)) [AddCommGroup L]
      [Module (Localization.AtPrime (q.asIdeal.comap (algebraMap R A))) L],
      Function.Injective
        (@LinearMap.lTensor _ _ L _ _ _ _ _ _
          (Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
            q.asIdeal (algebraMap R A) rfl))
          (Module.compHom _ (Localization.localRingHom (q.asIdeal.comap (algebraMap R A))
            q.asIdeal (algebraMap R A) rfl))
          (f.localizedAtContractedPrime (R := R) q)) := by
  sorry

end LinearMap
