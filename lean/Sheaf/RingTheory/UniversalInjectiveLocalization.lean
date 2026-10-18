/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization preserves universal injectivity

Source: Stacks Project, Algebra, Tag 05CM, `lemma-universally-injective-localize`,
part (1) (blueprint: lem-trf-local-universal-injective-localization).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w x y

namespace LinearMap

/-- If an `S`-linear map is universally injective after tensoring over `R`, then its
localization at a multiplicative submonoid of `S` is universally injective over `R`.
The localization is `LocalizedModule.map`, and universal injectivity is expanded as
injectivity after tensoring with every `R`-module. Source: Stacks Project, Algebra,
Tag 05CM, part (1) (blueprint: lem-trf-local-universal-injective-localization).

Proof:
1. Fix any `R`-module `L`. Put `v = 1_L ⊗ f`. The hypothesis says that `v` is
   injective. The actions on the second tensor factors make both tensor products
   `S`-modules and make `v` `S`-linear.
2. Apply `lem-weil-pbc-localization-tensor-over-base` (Mathlib's
   `IsLocalizedModule.rTensor`) and tensor symmetry to identify the localizations
   of `L ⊗[R] M` and `L ⊗[R] M'` with `L ⊗[R] LocalizedModule T M` and its target.
   These identifications send `(l ⊗ m)/t` to `l ⊗ (m/t)`. On pure fractions both
   composites in the resulting square send `(l ⊗ m)/t` to `l ⊗ (f m/t)`.
   Since pure tensors and fractions generate the modules, the square commutes.
3. Localization preserves injectivity by the fraction criterion of
   `def-weil-pbc-module-localization`: if `v(x)/t = 0`, some `s ∈ T` kills `v(x)`;
   `S`-linearity and injectivity give `s • x = 0`, so `x/t = 0`. Transport this
   injectivity through the two comparison isomorphisms. The resulting map is
   `(1_L ⊗ T⁻¹f)`, and `L` was arbitrary.
-/
theorem universally_injective_localizedModule_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
    [Module S M] [Module S M'] [Module R M] [Module R M']
    [IsScalarTower R S M] [IsScalarTower R S M']
    (T : Submonoid S) (f : M →ₗ[S] M')
    (hf : ∀ (L : Type (max u v w x y)) [AddCommGroup L] [Module R L],
      Function.Injective ((f.restrictScalars R).lTensor L)) :
    ∀ (L : Type (max u v w x y)) [AddCommGroup L] [Module R L],
      Function.Injective (((LocalizedModule.map T f).restrictScalars R).lTensor L) := by
  sorry

end LinearMap
