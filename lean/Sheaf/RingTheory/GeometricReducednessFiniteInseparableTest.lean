/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.FieldTheory.MakeSeparablyGenerated
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced

/-!
# Finite purely inseparable test for geometric reducedness

Source: Stacks Project, Algebra, Tag 030V, lemma-geometrically-reduced-finite-
purely-inseparable-extension, equivalence of (1) and (5)
(blueprint: lem-trf-geometric-reducedness-finite-inseparable-test).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- For an arbitrary commutative algebra over a field, reducedness after finite purely
inseparable field extensions is equivalent to reducedness after all field extensions.
Source: Stacks Project, Algebra, Tag 030V, lemma-geometrically-reduced-finite-
purely-inseparable-extension, equivalence of (1) and (5)
(blueprint: lem-trf-geometric-reducedness-finite-inseparable-test).

The proof follows Tag 030V.  Restriction to finite purely inseparable extensions is
immediate.  For the converse, a finitely generated field extension is placed in the
finite purely inseparable and separably generated square of
`lem-weil-pbc-make-separably-generated`; reducedness is preserved across its
separably generated upper edge by `lem-weil-pbc-separably-generated-tensor-reduced`,
and tensor cancellation identifies the resulting tensor product.  Flatness of a
module over a field descends reducedness along the finite extension.  Finally, any
nilpotent in a tensor product with an arbitrary field extension uses only finitely
many coefficients, so it descends to a finitely generated intermediate field and
the preceding argument applies.  The tensor products use their usual ring
multiplication and `IsReduced` means that every nilpotent element is zero.
-/
theorem isReduced_tensorProduct_iff_forall_finitePurelyInseparable
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C] :
    (∀ (E : Type (max u v)) [Field E] [Algebra k E]
      [Module.Finite k E] [IsPurelyInseparable k E],
      IsReduced (C ⊗[k] E)) ↔
      (∀ (K : Type (max u v)) [Field K] [Algebra k K],
        IsReduced (C ⊗[k] K)) := by
  sorry

end Algebra
