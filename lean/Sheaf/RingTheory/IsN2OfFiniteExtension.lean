/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.RingTheory.JapaneseDomain
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Descent of the Japanese condition along a finite extension of domains

Source: Stacks Project, Algebra, Lemma 10.161.7 (Tag 032K), N-2 clause
(blueprint: lem-weil-pbc-n2-descends-finite-domain-extension).
-/

universe uA uB uK uE

set_option autoImplicit false

/-- A Noetherian domain contained in a finite extension domain is Japanese if the larger
one is Japanese. Source: Stacks Project, Algebra, Lemma 10.161.7 (Tag 032K), N-2 clause
(blueprint: lem-weil-pbc-n2-descends-finite-domain-extension).

Proof (expanding the source's omitted proof and its integral-closure hint):
1. The inclusion `A → B` extends to an embedding `K → E` of fraction fields
   (`def-weil-pbc-localization-at-prime`). Fix a finite extension `L/K`
   (`def-pc-field-extension`); it suffices to show that `integralClosure A L` is finite.
2. Embed `L` over `K` in an algebraic closure of `E`, by
   `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed`, using
   `def-weil-algebraic-closure`. Finite-dimensional extensions are algebraic.
3. The compositum `M` of the images of `L` and `E` is finite over `E`, by
   `lem-weil-pbc-compositum-degree-bound`.
4. The embedding of `L` takes `integralClosure A L` into `integralClosure B M`:
   applying the embedding to a monic equation over `A` gives a monic equation over `B`
   (`def-weil-pbc-integral-closure`).
5. Since `B` is N-2 (`def-weil-pbc-japanese-domain`), `integralClosure B M` is finite
   over `B`, hence over `A` by `lem-weil-pbc-finite-module-over-finite-algebra` and
   `def-weil-finitely-generated-module`.
6. The image of `integralClosure A L` is an `A`-submodule of this finite module.
   Since `A` is Noetherian (`def-weil-pbc-noetherian-ring`), it is finite by
   `lem-weil-pbc-noetherian-submodule-finite`. The embedding is `A`-linear and injective,
   so `integralClosure A L` is finite as well. Varying `L` proves `IsN2 A K`. -/
theorem isN2_of_finite_extension (A : Type uA) (B : Type uB)
    (K : Type uK) (E : Type uE) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra B E] [IsFractionRing B E]
    (hAB : Function.Injective (algebraMap A B)) (hB : IsN2 B E) : IsN2 A K := by
  sorry
