/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicCompletion
import Mathlib.RingTheory.Smooth.Basic

/-!
# Adic formal smoothness of a completed polynomial local ring

For a Noetherian ring `A` and a prime `q` of `A[X]`, the completion of `A[X]_q` is formally smooth
over `A` for the `q`-adic topology.

## Implementation details

The polynomial ring is smooth and localization lifts across square-zero ideals, so `A[X]_q` is
formally smooth, hence `q`-adically formally smooth (Tag 07EC). Since `q` is finitely generated,
Tag 07ED passes to the completion. Noetherianity of the localization is not needed.

## References

* [Stacks, Tag 07PU]
* [Stacks, Tag 07EC]
* [Stacks, Tag 07ED]
* [Stacks, Tag 00TK]
* [Stacks, Tag 04EG]
* [Stacks, Tag 031H]
-/

@[expose] public section

universe u

namespace Algebra

/-- If `A` is Noetherian and `q` is a prime of `A[X]`, the completion of `A[X]` localized
at `q` is formally smooth over `A` for the topology defined by the extension of `q`.
The algebra structures are the canonical ones through the polynomial ring, localization,
and completion. -/
theorem polynomial_local_completion_formallySmoothAdic
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (q : Ideal (Polynomial A)) [q.IsPrime] :
    FormallySmoothAdic A
      (AdicCompletion (q.map (algebraMap (Polynomial A) (Localization.AtPrime q)))
        (Localization.AtPrime q))
      (q.map (algebraMap (Polynomial A)
        (AdicCompletion (q.map (algebraMap (Polynomial A) (Localization.AtPrime q)))
          (Localization.AtPrime q)))) := by
  let T := Localization.AtPrime q
  let n : Ideal T := q.map (algebraMap (Polynomial A) T)
  have hT : FormallySmoothAdic A T n := by
    intro D _ _ J hJ g _
    exact FormallySmooth.comp_surjective A T J hJ g
  have hn : n.FG := q.fg_of_isNoetherianRing.map _
  have hC := FormallySmoothAdic.adicCompletion A T n hn hT
  simpa only [n, Ideal.map_map, ← IsScalarTower.algebraMap_eq] using hC

end Algebra
