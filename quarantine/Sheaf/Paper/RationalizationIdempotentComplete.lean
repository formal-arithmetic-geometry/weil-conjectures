/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.RationalizationKaroubi
public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated
import WeilConjectures.CategoryTheory.Idempotents.TStructure
import Sheaf.Paper.ConstructibleHeart

/-!
# Idempotent completeness of rationalized constructible complexes

Source: Weil conjectures blueprint,
`sec-six-functors/sk-prop-sf-biduality-general/lem-weil-rationalization-idempotent-complete.md`,
order 2114 (blueprint: lem-weil-rationalization-idempotent-complete).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Idempotents AlgebraicGeometry

namespace WeilConjectures

/-- The raw rationalized constructible category is idempotent complete, and its canonical
functor to the Karoubi envelope is an exact equivalence.

Source: Weil conjectures blueprint,
`sec-six-functors/sk-prop-sf-biduality-general/lem-weil-rationalization-idempotent-complete.md`,
node order 2114 (blueprint: lem-weil-rationalization-idempotent-complete).

Proof: 1. Put `𝒯` equal to the raw rationalized category supplied by
`def-weil-rationalization-karoubi`. The standard-t-structure assertion of
`def-weil-constructible-heart`, as stated by
`rationalConstructibleStandardTStructure_existsUnique`, supplies a t-structure on this
precise category and its objectwise boundedness. Only these two witnesses are needed.
2. Apply `thm-weil-karoubian-bounded-t` to this triangulated category and bounded t-structure.
Its idempotent-completeness assertion splits every idempotent, while its equivalence assertion
says that the canonical `toKaroubi` functor is an exact equivalence. By
`def-weil-karoubi-envelope`, this is the stated canonical functor.
-/
theorem rationalization_idempotent_complete
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (_ι : E →ₐ[Padic l] Qbar)
    (Y : AlgebraicGeometry.Scheme.{u}) [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))] :
    IsIdempotentComplete (rationalConstructibleCategory D l hl E Y) ∧
      (toKaroubi (rationalConstructibleCategory D l hl E Y)).IsEquivalence ∧
        (toKaroubi (rationalConstructibleCategory D l hl E Y)).IsTriangulated := by
  obtain ⟨t, ⟨_, ht⟩, _⟩ :=
    rationalConstructibleStandardTStructure_existsUnique D l hl E Y
  exact ⟨t.isIdempotentComplete_of_bounded ht,
    t.isEquivalence_toKaroubi_and_isTriangulated_of_bounded ht⟩

end WeilConjectures
