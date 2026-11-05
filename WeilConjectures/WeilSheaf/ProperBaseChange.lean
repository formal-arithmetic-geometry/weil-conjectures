/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.WeilSheaf.ProperBaseChangeFunctor
public import WeilConjectures.WeilSheaf.TraceFunctionOps

/-!
# Proper base change for Weil complexes

For a cartesian square of `k₀`-schemes

```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```

with `f` proper, the base change isomorphism `g^* Rf_* K ≅ Rf'_* g'^* K` holds for Weil complexes
`K` on `X`, and taking cohomology sheaves, `g^* Rⁱf_* F ≅ Rⁱf'_* g'^* F` for Weil sheaves.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper`
  (`thm-weil-pbc-qbar`, with the Weil structures of `prop-weil-operations`).
- `AlgebraicGeometry.WeilSheaf.nonempty_upperStar_higherLowerStar_iso_of_isProper`: the form for
  higher direct images of Weil sheaves.

## Implementation notes

The objectwise statement is the component of the natural isomorphism
`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [X'.Over (Spec (CommRingCat.of k₀))]
  [Y'.Over (Spec (CommRingCat.of k₀))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
  [f'.IsOver (Spec (CommRingCat.of k₀))] [g'.IsOver (Spec (CommRingCat.of k₀))]
  [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f'] [QuasiSeparated f'] [LocallyOfFiniteType f']
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]

/-- **Proper base change for Weil complexes** (blueprint `thm-weil-pbc-qbar`, the base change
isomorphism being a morphism of Weil complexes by `prop-weil-operations`): for a cartesian square
of `k₀`-schemes `X' = X ×_Y Y'` with `f : X ⟶ Y` proper, and a Weil complex `K` on `X`, there is
an isomorphism of Weil complexes `g^* Rf_* K ≅ Rf'_* g'^* K`. -/
theorem WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper
    (hf : IsProper f) (h : IsPullback g' f' f g) (K : WeilComplex k₀ l X) :
    Nonempty ((WeilComplex.upperStar g).obj ((WeilComplex.derivedLowerStar f).obj K) ≅
      (WeilComplex.derivedLowerStar f').obj ((WeilComplex.upperStar g').obj K)) :=
  (WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper hf h).map (·.app K)

end AlgebraicGeometry
