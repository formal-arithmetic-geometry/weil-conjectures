/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Tate twists as tensor products of Weil complexes

The Tate twist `K ↦ K(m)` of Weil complexes (`AlgebraicGeometry.WeilComplex.tateTwist`) is
defined as the derived tensor product with the lisse Tate sheaf `ℚ̄_ℓ(m)`, through the derived
internal hom out of its dual. This file compares it, followed by a shift `[n]`, with the native
derived tensor product of Weil complexes
(`AlgebraicGeometry.WeilComplex.nativeConstructibleTensor`) with the Weil complex `ℚ̄_ℓ(m)[n]`
(`AlgebraicGeometry.WeilComplex.nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift`).

## Unfinished

The comparison is stated with `sorry`. Its proof needs the comparison of
`AlgebraicGeometry.WeilComplex.tensorLisse` (a derived internal hom out of the dual of a lisse
sheaf) with the native derived tensor product, which the library does not have yet, and the
compatibility of the native derived tensor product with shifts in its second variable.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Tate twists are tensor products** (blueprint: `def-wf-tate-twist`, where the Tate twist
`K(m) = K ⊗^L ℚ̄_ℓ(m)` is the derived tensor product with the Tate sheaf): for a Weil complex `K`
on `X`, the native derived tensor product `K ⊗ ℚ̄_ℓ(m)[n]` is the shifted Tate twist `K(m)[n]`,
naturally in `K`. -/
theorem nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift (m n : ℤ) :
    Nonempty ((𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const (WeilComplex k₀ l X)).obj
        (((tateTwist k₀ l X m).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦n⟧)) ⋙
          nativeConstructibleTensor k₀ l X ≅
      tateTwist k₀ l X m ⋙ shiftFunctor (WeilComplex k₀ l X) n) :=
  sorry

end AlgebraicGeometry.WeilComplex
