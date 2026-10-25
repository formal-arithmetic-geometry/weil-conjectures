/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Proper base change for Weil complexes, as an isomorphism of functors

For a cartesian square of `k₀`-schemes
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
with `f` proper, the base change morphism `g^* Rf_* ⟶ Rf'_* g'^*` of Weil complexes is a natural
isomorphism (blueprint `thm-weil-pbc-qbar`, the base change morphism being a morphism of Weil
complexes by `prop-weil-operations`). This theorem of the proper base change section is stated
here with `sorry`, as the existence of a natural isomorphism, in the form needed for the
compatibilities of the direct image with compact support
(`WeilConjectures.WeilSheaf.LowerShriekIndependence`); the objectwise statement is
`AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper`.
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

/-- **Proper base change for Weil complexes, naturally** (blueprint `thm-weil-pbc-qbar`, with the
Weil structures of `prop-weil-operations`): for a cartesian square of `k₀`-schemes
`X' = X ×_Y Y'` with `f : X ⟶ Y` proper, `g^* ∘ Rf_* ≅ Rf'_* ∘ g'^*` as functors of Weil
complexes on `X`. -/
theorem WeilComplex.nonempty_derivedLowerStar_comp_upperStar_iso_of_isProper
    (hf : IsProper f) (h : IsPullback g' f' f g) :
    Nonempty (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) f ⋙ WeilComplex.upperStar g ≅
      WeilComplex.upperStar g' ⋙ WeilComplex.derivedLowerStar f') :=
  sorry

end AlgebraicGeometry
