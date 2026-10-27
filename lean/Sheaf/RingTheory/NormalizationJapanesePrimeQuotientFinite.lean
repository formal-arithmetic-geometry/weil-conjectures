/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.RingTheory.JapaneseDomain

import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.TraceFormula.AlmostFiniteResidueFieldDegree

/-!
# Prime quotients of normalization over Japanese base quotients

Source: Marot, *Sur les anneaux universellement japonais*, Bulletin de la SMF 103
(1975), Lemma 1.1 and the standing hypotheses, printed p. 104
(blueprint: lem-per-normalization-japanese-prime-quotient-finite).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RingTheory

/-- A prime quotient of the integral closure in a finite fraction-field extension
is finite over the contracted base quotient when that quotient is Japanese.
The module structure is the canonical quotient algebra structure: its ring map is
`Ideal.quotientMap P (algebraMap R (integralClosure R L)) le_rfl`, which is injective
by `Ideal.quotientMap_injective`.

Source: Marot (1975), Lemma 1.1 and standing hypotheses, printed p. 104
(blueprint: lem-per-normalization-japanese-prime-quotient-finite).

Proof:
1. Put `T = integralClosure R L`, `p = P.comap (algebraMap R T)`, `A = R / p`,
   and `B = T / P`. The quotient map `A → B` is injective since its kernel is zero.
   The prime quotient `B` and its subring `A` are domains. The quotient `A` is
   Noetherian by `lem-weil-pbc-surjective-image-noetherian`. Extend the injection
   to the fraction fields `k = Frac(A)` and `E = Frac(B)`.
2. Apply `lem-trf-almost-finite-residue-field-degree` with `C = T`, `Q = P`,
   and `F = L`. Every element of `T` is integral over `R` by
   `def-weil-pbc-integral-closure`. Thus `E / k` is finite. The specified fraction
   field `K` can be identified with `FractionRing R` by fraction-field uniqueness.
3. Reduce a monic integral relation for each `t ∈ T` modulo `P`. This shows that
   `B` embeds as an `A`-submodule of `D = integralClosure A E`. The Japanese
   hypothesis `def-weil-pbc-japanese-domain` makes `D` finite over `A`.
4. Apply `lem-weil-pbc-noetherian-submodule-finite` to this submodule of the finite
   module `D` over the Noetherian ring `A`. This gives the asserted finiteness of `B`.
-/
theorem normalization_primeQuotient_finite_of_isN2
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L]
    (P : Ideal (integralClosure R L)) [P.IsPrime]
    (hJapanese : IsN2 (R ⧸ P.comap (algebraMap R (integralClosure R L)))
      (FractionRing (R ⧸ P.comap (algebraMap R (integralClosure R L))))) :
    Module.Finite (R ⧸ P.comap (algebraMap R (integralClosure R L)))
      ((integralClosure R L) ⧸ P) := by
  sorry

end RingTheory
