/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Geometric regularity under finitely generated field extensions

Source: Stacks Project, Algebra, Lemma 0381, implication (2) ⇒ (1)
(blueprint: lem-weil-pbc-geometrically-regular-finitely-generated-extensions).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- A geometrically regular Noetherian algebra remains Noetherian and regular after any
finitely generated field extension. Finite generation is as a field, not as an algebra.
Source: Stacks Project, Algebra, Lemma 0381, implication (2) ⇒ (1)
(blueprint: lem-weil-pbc-geometrically-regular-finitely-generated-extensions).

Proof from the node, following Stacks 0381:
1. Use lem-weil-pbc-make-separable (030R) to embed K in K' with finite purely inseparable
   extensions k'/k and K'/K and separable K'/k'. If K is generated over k by the a_i and
   the e_j form a finite K-basis of K', their images together generate K' over k'.
2. By lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra (037X), choose a
   smooth k'-subalgebra B of K' with fraction field K'; K' localizes B at its nonzero elements.
3. C = k' ⊗[k] A is regular by geometric regularity (def-weil-pbc-g-ring).
4. Smooth base change (lem-weil-pbc-smooth-ring-map-base-change-composition, 00T4) and
   smooth ascent (lem-weil-pbc-regular-ring-smooth-ascent, 07NF) make C ⊗[k'] B regular.
5. Base change of localization (lem-weil-pbc-localization-base-change) and two applications
   of lem-weil-pbc-tensor-cancel-base-change identify K' ⊗[k] A with a localization of
   C ⊗[k'] B. Use lem-weil-pbc-localization-of-regular-ring to obtain regularity.
6. The extension K'/K induces a faithfully flat map K ⊗[k] A → K' ⊗[k] A by
   lem-weil-pbc-field-extension-base-change-faithfully-flat and tensor cancellation.
   Descend regularity using lem-weil-pbc-regular-ring-faithfully-flat-descent (07NG).
   Regularity includes Noetherianity and regularity of every prime localization, as in
   def-weil-regular-scheme, so this gives both clauses of the conclusion. -/
theorem isRegularRing_tensorProduct_of_isGeometricallyRegular
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (hA : IsGeometricallyRegular k A)
    (K : Type w) [Field K] [Algebra k K]
    (hK : (⊤ : IntermediateField k K).FG) : IsRegularRing (TensorProduct k K A) := by
  sorry

end Algebra
