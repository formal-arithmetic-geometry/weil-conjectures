/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.KrullDimension

/-! # Dimension drop for a principal Cartier subscheme of an affine variety

Source: literature/stacks-project/algebra.tex, Tags 00KV and 00KW (Krull principal ideal
and height theorems), Tags 00OS and 00P0 (finite-type domain dimensions), and
literature/stacks-project/morphisms.tex, Tag 02FX (finite-type fibre dimension formula)
(blueprint: lem-sc-effective-cartier-affine-dimension-drop).
-/

universe u v

namespace AlgebraicGeometry

/-- Since a nonzero nonunit cuts an integral finite-type affine scheme by codimension one,
its principal quotient has Krull dimension one less.

Source: literature/stacks-project/algebra.tex, Tags 00KV, 00KW, 00OS and 00P0;
literature/stacks-project/morphisms.tex, Tag 02FX.
(blueprint: lem-sc-effective-cartier-affine-dimension-drop).

Proof:
1. Integrality of `Spec A` means that `A` is a domain (`affine_isIntegral_iff`), so `f ≠ 0`
   makes `f` a nonzerodivisor. Since `f` is not a unit, `(f)` is proper, the quotient is
   nonzero, and there is a maximal ideal containing `f`. Finite type over a field makes `A`
   Noetherian (`pqf-lem-locnoeth-lft`), as are its localizations at maximal ideals.
2. At every maximal ideal `m` containing `f`, the image of `f` remains a nonzerodivisor
   and lies in the maximal ideal of `A_m`. The local quotient dimension theorem
   (`lem-weil-pbc-dimension-quotient-nonzerodivisor`, Tag 00KW) gives
   `dim(A_m / f A_m) + 1 = dim(A_m)`. Every maximal localization of the finite-type
   domain `A` has the same finite dimension as `A`
   (`lem-weil-pbc-finite-type-domain-dimension-local-ring`, Tags 00OS and 00P0).
   Identify `A_m / f A_m` with the corresponding maximal localization of `A/(f)`.
3. Scheme dimension is the supremum of local-ring dimensions
   (`lem-pc-scheme-dimension-local-rings`). Every prime lies in a maximal ideal, and
   localization at that prime cannot increase the dimension of the maximal local ring.
   Thus the supremum can be taken over maximal ideals. Both spectra are nonempty;
   their maximal local rings have dimensions `dim(A)` and `dim(A) - 1`, respectively.
   Taking these suprema gives the asserted successor equality.
-/
theorem effective_cartier_affine_dimension_drop
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegral (Spec (CommRingCat.of A))]
    (f : A) (hf0 : f ≠ 0) (hfu : ¬ IsUnit f) :
    topologicalKrullDim
        (AlgebraicGeometry.Spec (CommRingCat.of (A ⧸ Ideal.span ({f} : Set A)))) + 1 =
      topologicalKrullDim (AlgebraicGeometry.Spec (CommRingCat.of A)) := by
  sorry

end AlgebraicGeometry
