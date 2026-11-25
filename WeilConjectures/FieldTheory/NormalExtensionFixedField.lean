/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable
import WeilConjectures.FieldTheory.NormalExtensionFixedFieldGalois

/-!
# The fixed field of all automorphisms of a normal extension

We show that for a normal extension `E/F` with fixed field `S = E ^ Aut(E/F)`, the extension `S/F`
is purely inseparable and `E/S` is Galois (`Normal.fixedField_purelyInseparable_and_galois`).

## Implementation details

The two halves are proved in `fixedField_purelyInseparable` and `fixedField_separable_normal`.
No finiteness of `Aut(E/F)` or `E/F` is required.

## References

* [Stacks Project, Lemma 030M](https://stacks.math.columbia.edu/tag/030M), part (2)
-/

@[expose] public section

universe u v

namespace Normal

/-- For a normal extension `E/F`, the intermediate field fixed by all `F`-automorphisms is purely
inseparable over `F`, and `E` is separable and normal over that fixed field. -/
theorem fixedField_purelyInseparable_and_galois
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [Normal F E] :
    IsPurelyInseparable F (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) ∧
      Algebra.IsSeparable (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E ∧
      Normal (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E := by
  let S := IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))
  have hp : IsPurelyInseparable F S :=
    fixedField_purelyInseparable F E
  have hg : Algebra.IsSeparable S E ∧ Normal S E :=
    fixedField_separable_normal F E
  exact ⟨hp, hg.1, hg.2⟩

end Normal
