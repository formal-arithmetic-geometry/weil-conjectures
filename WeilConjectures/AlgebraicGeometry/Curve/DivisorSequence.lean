/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence

/-!
# The divisor sequence of a punctured curve

Let `C̄` be a smooth proper connected curve over an algebraically closed field `k`, let
`S ⊆ C̄` be a finite set of closed points and `j : C = C̄ ∖ S ⟶ C̄` the open immersion of its
complement. Then

```
  0 ──▶ 𝔾ₘ ──▶ j_* 𝔾ₘ ──▶ ⨁_{P ∈ S} i_{P*} ℤ ──▶ 0
```

is a short exact sequence of étale sheaves on `C̄`, the third map sending a function on `C`
to its orders of vanishing at the punctures.

## Main statements

- `AlgebraicGeometry.IsCurve.exists_shortExact_divisorSequence`: the divisor sequence of a
  punctured curve is short exact. The proof is `sorry`.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **The divisor sequence of a punctured curve.** Let `C` be a smooth proper connected curve
over an algebraically closed field `k`, let `S` be a finite set of closed points of `C`, and
let `j : U ⟶ C` be an open immersion with image the complement of `S`. Then there is a map
`d` making

```
  0 ──▶ 𝔾ₘ ──▶ j_* 𝔾ₘ ──d──▶ ⨁_{P ∈ S} i_{P*} ℤ ──▶ 0
```

a short exact sequence of étale sheaves on `C`, where the first map is restriction of units
along `j` and the third term is the vertex of any colimit cocone `c` on the family
`P ↦ i_{P*} ℤ` of `AlgebraicGeometry.Scheme.pointConstantInt`. A connected curve has
dimension exactly one, which is the hypothesis `hC`; without it `S` could be all of
`C = Spec k`, where `j_* 𝔾ₘ = 0` but `𝔾ₘ ≠ 0`.

The sequence is exact on stalks: away from `S` the last term vanishes and `j_* 𝔾ₘ = 𝔾ₘ`; at
`P ∈ S` the strict henselisation `𝒪^{sh}_{C,P}` is a discrete valuation ring with fraction
field `K`, and the stalks are `1 ⟶ (𝒪^{sh}_{C,P})ˣ ⟶ Kˣ ⟶ ℤ ⟶ 0` via the normalised
valuation. The proof is `sorry`: stalks of étale sheaves as strict henselisations are not
available.
(blueprint: `lem-sc-divisor-exact-sequence`) -/
theorem exists_shortExact_divisorSequence (f : C ⟶ Spec (.of k)) [IsCurve f] [Smooth f]
    [IsProper f] [ConnectedSpace C] (hC : topologicalKrullDim C = 1) (S : Set C)
    (hS : S.Finite) (hSc : ∀ P ∈ S, IsClosed {P}) {U : Scheme.{u}} (j : U ⟶ C)
    [IsOpenImmersion j] (hj : Set.range j = Sᶜ)
    (c : Cofan fun P : S ↦ C.pointConstantInt P.1) (hc : IsColimit c) :
    ∃ (d : (Etale.lowerStar AddCommGrpCat.{u + 1} j).obj U.gmSheaf ⟶ c.pt)
      (w : Scheme.gmSheafToLowerStarGmSheaf j ≫ d = 0),
      (ShortComplex.mk (Scheme.gmSheafToLowerStarGmSheaf j) d w).ShortExact :=
  sorry

end AlgebraicGeometry.IsCurve
