/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Galois extensions receiving separable extensions, and normal extensions

* `exists_finiteDimensional_isGalois_algHom_of_isSeparable`: finitely many finite separable
  extensions `Lᵢ / k` embed into one finite Galois extension of `k`
  (Stacks, Lemmas 09DT and 0EXM).
* `Normal.isPurelyInseparable_fixedField_and_isGalois`: if `E / F` is normal and
  `E_insep = E ^ Aut(E/F)`, then `E_insep / F` is purely inseparable and `E / E_insep` is Galois
  (Stacks, Lemma 030M (2)).

## References

- Stacks Project, Lemma 09.15.1, <https://stacks.math.columbia.edu/tag/030M>
-/

@[expose] public section

open IntermediateField Polynomial

universe u v

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

