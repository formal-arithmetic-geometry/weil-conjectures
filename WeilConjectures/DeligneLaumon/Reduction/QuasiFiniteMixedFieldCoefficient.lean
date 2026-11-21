/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed
public import WeilConjectures.WeilSheaf.FieldCoefficientSheafExtendScalars

/-!
# Weil sheaves with coefficients in a finite extension of `ℚ_ℓ` on a quasi-finite scheme

A Weil complex with coefficients in a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` is called mixed if its
extension of scalars to `ℚ̄_ℓ` is. On a separated `k₀`-scheme quasi-finite over `k₀`, every
constructible `E`-Weil sheaf becomes mixed after extending scalars to any finite extension `E'`
of `E`, since every `ℚ̄_ℓ`-Weil sheaf there is mixed
(`AlgebraicGeometry.WeilSheaf.isMixed_of_locallyQuasiFinite`).

## Main statements

- `AlgebraicGeometry.FieldWeilSheaf.isMixed_toWeilSheaf_transition_of_locallyQuasiFinite`: the
  extension of scalars to `E'` of a constructible `E`-Weil sheaf on a quasi-finite `k₀`-scheme is
  mixed.
- `AlgebraicGeometry.WeilSheaf.isMixed_spec_and_isMixed_toWeilSheaf_transition`: Weil sheaves on
  `Spec k₀` are mixed, with coefficients in `ℚ̄_ℓ`, or after extension of scalars from `E` to `E'`.

## Implementation details

The extension of scalars to `E'` is not required to contain the eigenvalues of the Frobenius:
mixedness of an `E'`-Weil sheaf is tested after extending scalars to `ℚ̄_ℓ`, where every Weil
sheaf on a quasi-finite scheme is mixed.
-/

@[expose] public section

universe u

open CategoryTheory

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Let `X` be a separated `k₀`-scheme quasi-finite over `k₀`, `E ⊆ E'` finite extensions of
`ℚ_ℓ` inside `ℚ̄_ℓ` and `F` a constructible `E`-Weil sheaf on `X`. Then the extension of scalars
`E' ⊗_E F` is `ι`-mixed, that is, so is `ℚ̄_ℓ ⊗_{E'} (E' ⊗_E F)`. -/
theorem FieldWeilSheaf.isMixed_toWeilSheaf_transition_of_locallyQuasiFinite
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyQuasiFinite (X ↘ Spec (CommRingCat.of k₀))]
    (ι : PadicAlgCl l →+* ℂ) {E E' : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ E')
    (F : FieldWeilSheaf k₀ E.1 X) :
    ((FieldWeilSheaf.toWeilSheaf k₀ X E'.1).obj
      ((FieldWeilSheaf.transition k₀ X h).obj F)).IsMixed ι :=
  WeilSheaf.isMixed_of_locallyQuasiFinite ι _

/-- **Weil sheaves on a point are mixed.** Every constructible `ℚ̄_ℓ`-Weil sheaf on `Spec k₀`
is `ι`-mixed, and for finite extensions `E ⊆ E'` of `ℚ_ℓ` inside `ℚ̄_ℓ`, every constructible
`E`-Weil sheaf on `Spec k₀` becomes `ι`-mixed after extending scalars to `E'`. -/
theorem WeilSheaf.isMixed_spec_and_isMixed_toWeilSheaf_transition (ι : PadicAlgCl l →+* ℂ) :
    (∀ F : WeilSheaf k₀ l (Spec (CommRingCat.of k₀)), F.IsMixed ι) ∧
      ∀ {E E' : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ E')
        (F : FieldWeilSheaf k₀ E.1 (Spec (CommRingCat.of k₀))),
        ((FieldWeilSheaf.toWeilSheaf k₀ _ E'.1).obj
          ((FieldWeilSheaf.transition k₀ _ h).obj F)).IsMixed ι :=
  ⟨isMixed_of_locallyQuasiFinite ι, fun h F ↦
    FieldWeilSheaf.isMixed_toWeilSheaf_transition_of_locallyQuasiFinite ι h F⟩

end AlgebraicGeometry
