/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Algebraic spaces over fields are universally open

Source: Stacks Project, Morphisms of Spaces, Tag 06DN,
lemma-space-over-field-universally-open
(blueprint: lem-sfb-space-over-field-universally-open).

The product of sheaves on schemes over `Spec k` is the relative fibre product over `k`.
The point topology is the existing final topology for representable etale scheme charts.
Quantifying over arbitrary algebraic spaces `Y` gives every algebraic-space base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The second projection from the sheaf fibre product of two algebraic spaces over a
field is open on their point spaces, without any finiteness or nonemptiness assumption.
Source: Stacks Project, Morphisms of Spaces, Tag 06DN; Properties of Spaces, Tags 03H4
and 03BX (blueprint: lem-sfb-space-over-field-universally-open).

Proof:
1. Choose a representable surjective etale scheme atlas `U → X` using
   def-trf-algebraic-space. For any scheme `V` over `k`, its base change
   `U ×_k V → X ×_k V` is surjective etale by lem-trf-space-fibre-products-etale-covers.
   Its point map is continuous and surjective by lem-a1-space-point-open-calculus.
2. The scheme projection `U ×_k V → V` is open by
   lem-sc-scheme-over-field-universally-open. For an open `W` in `|X ×_k V|`, its image
   in `|V|` is the image of the open atlas inverse image of `W`, by atlas surjectivity.
   This proves openness for scheme base changes, including empty schemes.
3. For an arbitrary algebraic space `Y`, test the image of an open `O` in `|X ×_k Y|`
   along every representable etale scheme chart `V → Y`. Pullback associativity from
   lem-trf-space-fibre-products-etale-covers identifies the pulled-back space with
   `X ×_k V`. The compatible-point lifting clause of lem-a1-space-point-open-calculus
   identifies the inverse image of the image of `O` with the image of its inverse image
   in `|X ×_k V|`. This is open by step 2, since the other point projection is continuous.
   The final-topology criterion of def-a1-space-point-topology therefore makes the image
   of `O` open in `|Y|`. Since `Y` was arbitrary, this is universal openness. -/
theorem isOpenMap_prod_snd_overField (k : Type u) [Field k]
    (X Y : AlgebraicSpace (Spec (CommRingCat.of k))) :
    IsOpenMap (mapPoint (Limits.prod.snd (X := X.obj) (Y := Y.obj)).hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
