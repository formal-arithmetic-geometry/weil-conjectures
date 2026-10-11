/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.RingTheory.FormallySmoothAdic

/-!
# Adic formal smoothness of a completed polynomial local ring

Source: Stacks Project, More on Algebra, proof of Lemma 15.51.9 (Tag 07PU),
via Lemmas 15.38.2 (Tag 07EC) and 15.38.4 (Tag 07ED)
(blueprint: lem-weil-pbc-polynomial-local-completion-formally-smooth).
-/

universe u

namespace Algebra

/-- If `A` is Noetherian and `q` is a prime of `A[X]`, the completion of `A[X]` localized
at `q` is formally smooth over `A` for the topology defined by the extension of `q`.
The algebra structures are the canonical ones through the polynomial ring, localization,
and completion. Source: Stacks Project, proof of Tag 07PU, using Tags 07EC(1) and 07ED.
(blueprint: lem-weil-pbc-polynomial-local-completion-formally-smooth)

Proof:
1. The polynomial algebra `A[X]` is smooth, hence has square-zero lifting
   (`lem-weil-pbc-polynomial-ring-smooth`,
   `lem-weil-pbc-smooth-ring-map-square-zero-lifting`; Tag 00TK).
2. Given a lifting problem for `T = A[X]_q`, first restrict to `A[X]` and lift there.
   Localization lifts across square-zero ideals, extending that lift to `T`
   (`lem-weil-pbc-localization-square-zero-lifting`,
   `def-weil-pbc-algebra-hom-quotient`; Tags 04EG and 031H).
3. Discrete formal smoothness implies formal smoothness for the `qT`-adic topology:
   it supplies a lift even without requiring the initial map to kill a power of `qT`
   (`def-weil-pbc-formally-smooth-adic`; Tag 07EC(1)).
4. The polynomial ring is a finite type algebra over the Noetherian ring `A`, hence
   Noetherian, and so is its localization. Thus `qT` is finitely generated
   (`lem-weil-pbc-finite-type-algebra-noetherian`,
   `lem-weil-pbc-localization-noetherian`, `def-weil-pbc-noetherian-ring`).
5. Apply `lem-weil-pbc-fs-adic-completion` (Tag 07ED(1) implies (2)) to obtain formal
   smoothness of the completion for the extended ideal `(qT)C`. This equals `qC`:
   elements of `qT` are fractions with numerator in `q` and denominator outside `q`,
   and the inverses of those denominators also map into `C`
   (`def-weil-pbc-adic-completion`, `def-weil-pbc-localization-at-prime`).
-/
theorem polynomial_local_completion_formallySmoothAdic
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (q : Ideal (Polynomial A)) [q.IsPrime] :
    FormallySmoothAdic A
      (AdicCompletion (q.map (algebraMap (Polynomial A) (Localization.AtPrime q)))
        (Localization.AtPrime q))
      (q.map (algebraMap (Polynomial A)
        (AdicCompletion (q.map (algebraMap (Polynomial A) (Localization.AtPrime q)))
          (Localization.AtPrime q)))) := by
  sorry

end Algebra
