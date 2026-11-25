/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.EssentialFiniteness
import WeilConjectures.FieldTheory.SmoothFractionFieldLocalizations
import WeilConjectures.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Finitely generated separable extensions and smooth subalgebras

A finitely generated separable field extension `L/K` is the directed union of its finitely
generated smooth `K`-subalgebras.

## Main results

- `FieldTheory.fg_separable_extension_is_filtered_colimit_smooth`

## Implementation details

One chooses a smooth `K`-subalgebra `B` of `L` with fraction field `L`; the principal
localizations `B[1/f]`, `f ≠ 0`, are smooth, finitely generated and directed, with union `L`.

## References

* Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV.
-/

@[expose] public section

universe u v

namespace FieldTheory

/--
For a finitely generated separable extension of fields `L/K`, the field `L` is
the filtered colimit of its finitely generated smooth `K`-subalgebras, with
the transition maps given by inclusions: there is a nonempty directed family `A` of finitely
generated smooth `K`-subalgebras of `L` whose union is `L`.
-/
theorem fg_separable_extension_is_filtered_colimit_smooth
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hsep : Algebra.IsSeparableExtension K L) [Algebra.EssFiniteType K L] :
    ∃ (ι : Type v) (A : ι → Subalgebra K L),
      Nonempty ι ∧
        (∀ i, Algebra.Smooth K (A i)) ∧
        (∀ i, (A i).FG) ∧
        Directed (· ≤ ·) A ∧
        ∀ x : L, ∃ i, x ∈ A i := by
  obtain ⟨B, hBsm, hfrac⟩ := exists_smooth_subalgebra_fraction_field
    (IntermediateField.fg_top_iff.mpr inferInstance) hsep
  exact exists_smooth_fg_localization_family B hBsm hfrac

end FieldTheory
