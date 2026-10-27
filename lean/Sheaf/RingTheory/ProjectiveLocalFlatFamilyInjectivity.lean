/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Sheaf.RingTheory.LocalUniversalInjectiveResidue

/-! # Projective modules detected by flat local families

Source: Stacks Project, Tag 05FQ, lemma-universally-injective-local, applied prime by
prime to the product argument in Tag 0810, lemma-helper-blowup-affine-space, final paragraph.
(blueprint: lem-trf-projective-local-flat-family-injectivity).

## Main declarations

* `LinearMap.liftToPrimeLocalization`: the canonical map `M_p → N` induced by `M → N`.
* `Module.projective_local_flat_family_injectivity`: localized projectivity, universal
  injectivity of the induced maps, and injectivity into the product of the local targets.
-/

@[expose] public section

universe u v w z

namespace LinearMap

/-- Extend an `R`-linear map into an `R_p`-module to the localization of its source.
This is Mathlib's localization lift, promoted to `R_p`-linearity; on fractions it sends
`x/s` to `s⁻¹ • v x`, and on `x/1` it equals `v x` (`LocalizedModule.lift_mk`).
The compatible `R`-module structure on `N` is restriction of scalars from `R_p`.
Source: Stacks Project, Tag 07JZ, module localization, and Tag 05FQ, local application.
(blueprint: lem-trf-projective-local-flat-family-injectivity). -/
noncomputable def liftToPrimeLocalization
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) {N : Type w} [AddCommGroup N]
    [Module R N] [Module (Localization.AtPrime p.asIdeal) N]
    [IsScalarTower R (Localization.AtPrime p.asIdeal) N] (v : M →ₗ[R] N) :
    LocalizedModule p.asIdeal.primeCompl M →ₗ[Localization.AtPrime p.asIdeal] N :=
  (LocalizedModule.lift p.asIdeal.primeCompl v
    (isLocalizedModule_id p.asIdeal.primeCompl N
      (Localization.AtPrime p.asIdeal)).map_units).extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)

end LinearMap

namespace Module

/-- A projective module is detected by flat targets over its prime localizations when
all induced residue maps are injective. Residue-field tensor products canonically identify
with quotients modulo the maximal ideal, so `hres` is precisely the quotient-map hypothesis.
No finite-generation assumption is imposed on `M` or on the local targets.

Source: Stacks Project, Tag 05FQ, lemma-universally-injective-local, and Tag 0810,
lemma-helper-blowup-affine-space, final paragraph.
(blueprint: lem-trf-projective-local-flat-family-injectivity).

Proof:
1. For each prime `p`, localization preserves projectivity without a finiteness hypothesis
   (lem-weil-pbc-localization-projective), so `M_p` is projective over `R_p`.
2. Apply lem-trf-local-universal-injective-residue over the local ring `R_p` to the
   canonical `liftToPrimeLocalization p (v p)`. Step 1 gives projectivity, while flatness
   and residue injectivity are hypotheses. This proves injectivity after tensoring with
   every `R_p`-module `L`.
3. Take `L = R_p`. The canonical isomorphism `R_p ⊗[R_p] T ≃ T`, given by scalar
   multiplication with inverse `t ↦ 1 ⊗ t`, identifies this tensor map with the local map.
   Therefore every local map is injective (def-weil-pbc-module-tensor-product).
4. If `x` is in the kernel of `LinearMap.pi v`, then its image `x/1` in every `M_p`
   vanishes by step 3 and `LocalizedModule.lift_mk_one`. If `x ≠ 0`, its annihilator is
   proper. Choose a prime containing it (lem-weil-pbc-minimal-prime-over-proper-ideal).
   The localization zero criterion (def-weil-pbc-module-localization) gives a denominator
   `s` outside this prime with `s • x = 0`, contradicting containment of the annihilator.
   Thus the product map has zero kernel and is injective by applying this to differences.
-/
theorem projective_local_flat_family_injectivity
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Projective R M]
    (N : PrimeSpectrum R → Type w) [∀ p, AddCommGroup (N p)]
    [∀ p, Module R (N p)] [∀ p, Module (Localization.AtPrime p.asIdeal) (N p)]
    [∀ p, IsScalarTower R (Localization.AtPrime p.asIdeal) (N p)]
    [∀ p, Module.Flat (Localization.AtPrime p.asIdeal) (N p)]
    (v : ∀ p, M →ₗ[R] N p)
    (hres : ∀ p, Function.Injective
      ((LinearMap.liftToPrimeLocalization p (v p)).lTensor
        (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)))) :
    (∀ p : PrimeSpectrum R,
      Module.Projective (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) ∧
    (∀ (p : PrimeSpectrum R) (L : Type (max u v w z)) [AddCommGroup L]
      [Module (Localization.AtPrime p.asIdeal) L],
      Function.Injective ((LinearMap.liftToPrimeLocalization p (v p)).lTensor L)) ∧
    Function.Injective (LinearMap.pi v) := by
  sorry

end Module
