/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.NagataRing
import Sheaf.RingTheory.FiniteTypeGRing
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.RegularRingNormal
import Sheaf.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.IsN1OfIsAnalyticallyUnramified
import WeilConjectures.RingTheory.AnalyticallyUnramified
import Sheaf.RingTheory.IsN1OfLocalCharacterization
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.RegularMapReducedTarget
import Sheaf.RingTheory.UniversallyJapaneseN1Criterion
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Quasi-excellent rings are Nagata

Source: Stacks Project, More on Algebra, Lemma Tag 07QV
(blueprint: lem-exc-quasi-excellent-nagata).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- Every commutative quasi-excellent ring is Nagata.

Source: Stacks Project, More on Algebra, Lemma Tag 07QV
(blueprint: lem-exc-quasi-excellent-nagata).

Proof:
1. Let `S` be any finite type domain algebra over `R`. The G-ring clause of
   `def-exc-excellent-ring` and `lem-weil-pbc-finite-type-over-g-ring` make `S` a
   Noetherian G-ring (`def-weil-pbc-g-ring`). We show that `S` is N-1.
2. The J-2 clause says the regular locus of `Spec S` is open. The zero-prime
   localization is the fraction field (`def-weil-pbc-localization-at-prime`), which
   is regular (`lem-weil-pbc-field-regular-ring`). The closed complement is `V(I)`
   by `lem-weil-pbc-spec-irreducible-closed-subsets-primes`. Since it misses the
   zero prime, some nonzero `f` lies in `I`; then `D(f)` is contained in the regular
   locus (`def-weil-affine-spectrum`).
3. The ring `S_f` (`def-weil-ring-localization-away`) is Noetherian by
   `lem-weil-pbc-localization-noetherian`. A prime `Q` contracts to a prime `p`
   outside `f` (`lem-weil-pbc-localization-spectrum-embedding`). The local rings
   `(S_f)_Q` and `S_p` are isomorphic: on fractions the maps are
   `a/u ↦ (a/1)/(u/1)` and `(a/f^n)/(b/f^m) ↦ a*f^m/(b*f^n)`.
   The localization equality criteria make these well-defined inverse maps.
   Thus every prime localization is regular local. By `def-weil-regular-scheme`
   and `lem-weil-pbc-regular-ring-normal`, the principal localization is normal.
4. For every maximal ideal `m` of `S`, put `A = S_m`. This is Noetherian local,
   and is a domain: a zero product of fractions gives `w*a*b = 0` for a nonzero
   denominator `w`, hence one numerator is zero. Its maximal-ideal completion
   map is regular by `def-weil-pbc-g-ring`, and its completion is Noetherian by
   `lem-weil-pbc-adic-completion-noetherian`. Apply
   `lem-exc-regular-map-reduced-target` to the reduced domain `A` to see that
   this completion is reduced.
5. Apply `lem-weil-pbc-analytically-unramified-n1` to each such `A`. It follows
   that every maximal localization of `S` is N-1.
6. Apply `lem-weil-pbc-n1-local-characterization` to the nonzero `f` from step 2,
   its normal principal localization from step 3, and the local N-1 conclusion
   of step 5. Hence `S` is N-1. This holds for every finite type domain algebra.
7. By `lem-exc-universally-japanese-n1-criterion`, `R` is universally Japanese:
   every finite type domain algebra is N-2.
8. For any prime `p` of `R`, the quotient `R/p` is a domain and is a finite type
   `R`-algebra (no generators are needed, `def-weil-pbc-finite-type-algebra`).
   Step 7 makes it N-2. Together with Noetherianity from quasi-excellence these
   are exactly the two clauses of `def-weil-pbc-nagata-ring`.
-/
theorem isNagataRing_of_isQuasiExcellent (R : Type u) [CommRing R]
    (hR : IsQuasiExcellent R) : IsNagataRing R := by
  sorry
