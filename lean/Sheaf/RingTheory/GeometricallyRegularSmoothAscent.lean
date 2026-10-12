/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.RegularRingSmoothAscent

/-!
# Geometric regularity ascends along smooth algebra maps

Source: Stacks Project, Algebra, Lemma 07QF
(blueprint: lem-weil-pbc-geometrically-regular-smooth-ascent).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Smooth maps of algebras over a field preserve Noetherianity and geometric regularity.
Source: Stacks Project, Algebra, Lemma 07QF
(blueprint: lem-weil-pbc-geometrically-regular-smooth-ascent).

Proof:
1. Smoothness gives finite presentation, hence finite type. Since A is Noetherian, B is
   Noetherian by lem-weil-pbc-finite-type-algebra-noetherian (Stacks 00FN).
2. For any finite purely inseparable extension k'/k, geometric regularity of A says that
   k' ⊗[k] A is regular, by def-weil-pbc-g-ring (Stacks 0381, condition (2)).
3. Base change of the smooth map gives a smooth map from k' ⊗[k] A to k' ⊗[k] B, using
   lem-weil-pbc-smooth-ring-map-base-change-composition (Stacks 00T4) and
   lem-weil-pbc-tensor-cancel-base-change. Transport smoothness across the tensor-product
   identification using Algebra.Smooth.of_equiv.
4. Regularity ascends along this smooth map, by lem-weil-pbc-regular-ring-smooth-ascent
   (Stacks 07NF), so k' ⊗[k] B is regular.
5. Together with step 1, this is geometric regularity of B by def-weil-pbc-g-ring.
-/
theorem isGeometricallyRegular_of_smooth
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B)
    (hsmooth : letI : Algebra A B := φ.toRingHom.toAlgebra; Algebra.Smooth A B)
    (hnoetherian : IsNoetherianRing A) (hregular : IsGeometricallyRegular k A) :
    IsNoetherianRing B ∧ IsGeometricallyRegular k B := by
  sorry

end Algebra
