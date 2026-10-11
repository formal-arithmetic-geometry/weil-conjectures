/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local filtered colimits of etale algebras over normal domains

Source: Stacks Project, Tag 06DI, proof of normality of strict henselizations,
with Tags 033C, 037D, 00GV, 00U2 and 00D7
(blueprint: lem-weil-pbc-etale-colimit-normal-local-domain).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- A local filtered colimit of etale algebras over a normal domain is an integrally
closed domain, and its structure map is injective. Source: Stacks Project, Tag 06DI,
normality implication, and Tags 00U2 and 00D7 for injectivity
(blueprint: lem-weil-pbc-etale-colimit-normal-local-domain).

Proof:
1. By `lem-weil-pbc-filtered-colimit-algebras-elementwise`, the algebra colimit is also
   the colimit of the underlying commutative rings, with the same coprojections.
2. Each diagram ring is normal by `lem-weil-pbc-etale-over-normal-ring-normal`:
   etale maps are smooth, and normality ascends along smooth maps (Tag 033C).
3. By `lem-weil-pbc-filtered-colimit-normal-ring`, the colimit ring is normal (Tag 037D).
4. A local normal ring is a normal domain: localization at its maximal ideal is
   isomorphic to the ring since every denominator outside that ideal is a unit.
   Thus the domain and integral-closedness properties of that localization transfer back
   (`def-weil-pbc-normal-ring`, Tag 00GV).
5. By `lem-weil-pbc-etale-algebra-flat` and `def-weil-pbc-flat-ring-map`, each diagram
   ring is flat over the domain A. Multiplication by any nonzero element of A is
   injective on A, hence on each diagram ring by tensoring with that flat algebra.
6. If a nonzero element of A dies in the colimit, choose an object of the nonempty
   filtered category. By `lem-weil-pbc-filtered-colimit-rings-zero`, its image dies
   at some later stage. Injectivity of multiplication forces that stage to be the zero
   ring, so its unital coprojection forces the colimit to be zero, contradicting locality.
   Hence the structure map is injective. -/
theorem isDomain_isIntegrallyClosed_injective_of_etale_colimit
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{v} A) [HasColimit B]
    (hB : ∀ i : I, Algebra.Etale A (B.obj i)) [IsLocalRing ↥(colimit B)] :
    (IsDomain ↥(colimit B) ∧ IsIntegrallyClosed ↥(colimit B)) ∧
      Function.Injective (algebraMap A ↥(colimit B)) := by
  sorry

end CommAlgCat
