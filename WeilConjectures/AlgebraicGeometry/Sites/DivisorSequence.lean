/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The divisor sequence and the generic-point injection for the Brauer group

For an integral regular noetherian scheme `X` with generic point `i : Spec k(X) ⟶ X` there is
a short exact sequence of étale sheaves

```
  0 ──▶ 𝔾ₘ ──unit──▶ i_* i^* 𝔾ₘ ──div──▶ ∐_{x ∈ X⁽¹⁾} i_{x*} ℤ ──▶ 0
```

the third map sending a rational function to its divisor. The points of `X⁽¹⁾` are the points
of coheight one, and `i_{x*} ℤ` is the pushforward of the constant sheaf `ℤ` along
`Spec κ(x) ⟶ X`. Taking the long exact cohomology sequence and using
`H¹(X, i_{x*} ℤ) = 0` gives Grothendieck's residue injection

```
   Spec k(X) ──── i ────▶ X            H²(X_ét, 𝔾ₘ)
                                            │ cohomologyMap i 𝔾ₘ 2  (injective)
                                            ▼
                                       H²(Spec k(X)_ét, i^* 𝔾ₘ)
```

whose target is `H²(Spec k(X)_ét, 𝔾ₘ) = Br(k(X))` by
`AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`.

## Main definitions

- `AlgebraicGeometry.Scheme.genericGm`: the sheaf `i_* i^* 𝔾ₘ`.
- `AlgebraicGeometry.Scheme.toGenericGm`: the unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ`, the first map of the
  divisor sequence.
- `AlgebraicGeometry.Scheme.pointConstantInt`: the sheaf `i_{x*} ℤ` of a point `x` of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`: the
  pullback of `𝔾ₘ` along the generic point is `𝔾ₘ`. The proof is `sorry`.
- `AlgebraicGeometry.Scheme.exists_shortExact_divisorSequence`: the divisor sequence is short
  exact.
- `AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two`: the map
  `Br(X) = H²(X, 𝔾ₘ) → H²(Spec k(X), 𝔾ₘ) = Br(k(X))` along the generic point is injective.

## TODO

The divisor map itself is not named: `exists_shortExact_divisorSequence` asserts that *some*
map `div` out of `i_* i^* 𝔾ₘ` makes the sequence short exact, rather than that the map
`f ↦ ∑_{x ∈ X⁽¹⁾} ord_x(f) [x]` built from `AlgebraicGeometry.Scheme.ord` does. The first map
is pinned down, since it is the one that Grothendieck's residue argument uses.

The third term is a colimit cocone taken as an argument rather than the coproduct
`∐ fun x ↦ X.pointConstantInt x`. The sheaf category is Grothendieck abelian, so the
coproduct does exist, but synthesising `Limits.HasCoproduct` for a family indexed by a type
in the universe of the points of `X` does not terminate in a usable time here; it should be
replaced by `∐ …` once that is fixed.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits Order

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The étale sheaf `i_* i^* 𝔾ₘ` on `X`, the pushforward along the generic point
`i : Spec k(X) ⟶ X` of the pullback of `𝔾ₘ`. It is written this way, rather than as the
pushforward of the sheaf `𝔾ₘ` of `Spec k(X)`, so that the unit
`AlgebraicGeometry.Scheme.toGenericGm` of the adjunction lands in it by construction; the
comparison of the two is `AlgebraicGeometry.Scheme.genericGmIso`. -/
noncomputable def genericGm : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
    ((Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf)

/-- The unit `𝔾ₘ ⟶ i_* i^* 𝔾ₘ` of the adjunction
`AlgebraicGeometry.Etale.upperStarLowerStarAdjunction` at the generic point: the first map of
the divisor sequence. -/
noncomputable def toGenericGm : X.gmSheaf ⟶ X.genericGm :=
  (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField).unit.app
    X.gmSheaf

/-- The comparison map `i^* 𝔾ₘ ⟶ 𝔾ₘ` along the generic point `i : Spec k(X) ⟶ X` is an
isomorphism. The morphism `i` is not étale, but both sheaves have stalk `(k(X)ˢᵉᵖ)ˣ` at a
separable closure of `k(X)`: the strict henselisation of the local ring `𝒪_{X,η} = k(X)` is
`k(X)ˢᵉᵖ`. The proof is `sorry`. -/
theorem isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField :
    IsIso (upperStarGmSheafToGmSheaf X.fromSpecFunctionField) :=
  sorry

/-- The sheaf `i_* i^* 𝔾ₘ` is the pushforward of the sheaf `𝔾ₘ` of `Spec k(X)`, because the
pullback of `𝔾ₘ` along the generic point is `𝔾ₘ`
(`AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`). -/
noncomputable def genericGmIso : X.genericGm ≅
    (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
      (Spec X.functionField).gmSheaf :=
  haveI := X.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).mapIso
    (asIso (upperStarGmSheafToGmSheaf X.fromSpecFunctionField))

/-- The étale sheaf `i_{x*} ℤ` on `X`: the pushforward of the constant sheaf `ℤ` along the
canonical morphism `Spec κ(x) ⟶ X` of a point `x` of `X`. -/
noncomputable def pointConstantInt (x : X) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).obj
    ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- **The divisor sequence.** Let `X` be an integral regular locally noetherian scheme with
generic point `i : Spec k(X) ⟶ X`, and let `X⁽¹⁾` be its set of coheight-one points. Then
there is a divisor map `div` making

```
  0 ──▶ 𝔾ₘ ──unit──▶ i_* i^* 𝔾ₘ ──div──▶ ∐_{x ∈ X⁽¹⁾} i_{x*} ℤ ──▶ 0
```

a short exact sequence of étale sheaves on `X`, where the third term is the vertex of any
colimit cocone `c` on the family `x ↦ i_{x*} ℤ`. The first map is pinned down as the unit
`AlgebraicGeometry.Scheme.toGenericGm`, which is the form the residue argument of
`AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two` uses; `div` itself is only
asserted to exist, see the TODO in the module docstring. The proof is `sorry`.
(blueprint: `lem-sc-divisor-sequence-general`) -/
theorem exists_shortExact_divisorSequence [IsLocallyNoetherian X] [IsRegular X]
    (c : Cofan fun x : {x : X // coheight x = 1} ↦ X.pointConstantInt x.1) (hc : IsColimit c) :
    ∃ (d : X.genericGm ⟶ c.pt) (w : X.toGenericGm ≫ d = 0),
      (ShortComplex.mk X.toGenericGm d w).ShortExact :=
  sorry

/-- **Grothendieck's residue injection for the Brauer group.** Let `X` be an integral regular
noetherian scheme with function field `k(X)`. Then the pullback along the generic point
`i : Spec k(X) ⟶ X`

```
   Spec k(X) ──── i ────▶ X            H²(X_ét, 𝔾ₘ)
                                            │ cohomologyMap i 𝔾ₘ 2
                                            ▼
                                       H²(Spec k(X)_ét, i^* 𝔾ₘ)
```

is injective, that is, `Br(X) = H²(X, 𝔾ₘ) ↪ H²(Spec k(X), 𝔾ₘ) = Br(k(X))`; the target is
identified with the cohomological Brauer group of `k(X)` by
`AlgebraicGeometry.Scheme.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField`. It follows from the long exact cohomology
sequence of the divisor sequence together with `H¹(X, i_{x*} ℤ) = 0`. In particular this
holds for a smooth curve. The proof is `sorry`.
(blueprint: `lem-sc-brauer-injectivity`) -/
theorem injective_cohomologyMap_gmSheaf_two [IsNoetherian X] [IsRegular X] :
    Function.Injective (Etale.cohomologyMap X.fromSpecFunctionField X.gmSheaf 2) :=
  sorry

end AlgebraicGeometry.Scheme
