/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# Ample invertible modules and the Hilbert degree

An invertible `𝒪_X`-module is *very ample* over a field `K` if it is the pullback of `𝒪(1)`
along a closed immersion of `X` into a projective space over `K`, and *ample* if some positive
tensor power of it is very ample. For an ample invertible module `M` on a proper `K`-scheme `X`
of dimension `g`, the function `m ↦ χ(X, M^{⊗ m})` is a numerical polynomial of degree at most
`g`, and the *degree of `X` with respect to `M`* is `g!` times its leading coefficient.

The Euler characteristic of a coherent sheaf is not available in Mathlib, so
`AlgebraicGeometry.Scheme.Hom.degree` is declared here as an `opaque` constant. Being `opaque`
rather than `sorry`-bodied it depends genuinely on its arguments and introduces no `sorryAx`;
but it satisfies no equations whatsoever, so **none of the statements below can be proved
before it is replaced**.

## Main definitions

- `AlgebraicGeometry.IsVeryAmple`, `AlgebraicGeometry.IsAmple`: very ample and ample invertible
  modules on a scheme over a field.
- `AlgebraicGeometry.Scheme.Hom.degree`: the degree of a proper scheme with respect to an ample
  invertible module.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple`: an ample invertible module on a proper
  curve has positive degree.
- `AlgebraicGeometry.Scheme.Hom.degree_pullback`: the degree multiplies by the degree of the
  morphism under pullback along a finite surjective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- An `𝒪_X`-module `M` is *very ample* over `K` if it is the pullback of `𝒪(1)` along a
closed immersion `i : X ⟶ ℙ(n; Spec K)` over `K` into a projective space with finitely many
homogeneous coordinates.

(blueprint: `sk-def-av-ample-degree`) -/
def IsVeryAmple (f : X ⟶ Spec (.of K)) (M : X.Modules) : Prop :=
  ∃ (n : Type u) (_ : Finite n) (i : X ⟶ ℙ(n; Spec (.of K))), IsClosedImmersion i ∧
    i ≫ (ℙ(n; Spec (.of K)) ↘ Spec (.of K)) = f ∧
    Nonempty ((Scheme.Modules.pullback i).obj (ProjectiveSpace.twist n _ 1) ≅ M)

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An invertible `𝒪_X`-module is *ample* if some positive tensor power of it is very ample. -/
def IsAmple (f : X ⟶ Spec (.of K)) (M : X.Modules) : Prop :=
  ∃ m : ℕ, 0 < m ∧ IsVeryAmple f (M.tensorPow m)

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

The degree of a proper `K`-scheme `X` of dimension `g` with respect to an ample invertible
`𝒪_X`-module `M`: `g!` times the leading coefficient of the Hilbert polynomial
`m ↦ χ(X, M^{⊗ m})`.

The Euler characteristic of a coherent sheaf is not available in Mathlib, so this is an
`opaque` placeholder; it satisfies no equations. -/
-- TODO(unify): sk-def-av-ample-degree
opaque Scheme.Hom.degree (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℤ

/-- Blueprint `sk-prop-av-ample-positive`: Ample modules on proper curves have positive degree.

Let `K` be algebraically closed, `C` a proper curve over `K` of dimension one (possibly
disconnected) and `L` an ample invertible `𝒪_C`-module. Then `deg L > 0`. -/
theorem Scheme.Hom.degree_pos_of_isAmple [IsAlgClosed K] (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) (L : X.Modules) [L.IsInvertible] (hample : IsAmple f L) :
    0 < f.degree L :=
  sorry

/-- Blueprint `sk-prop-av-deg-pullback`: Degree of a pullback under a finite morphism.

Let `g : X ⟶ Y` be a finite surjective morphism of proper `K`-varieties of the same dimension,
let `M` be an ample invertible `𝒪_Y`-module and let `d = [k(X) : k(Y)]` be the degree of `g`.
Then `deg_{g^*M}(X) = d * deg_M(Y)`.

```
  X ────────── g ─────────▶ Y
    ╲                       │
     ╲  fX                  │ fY
      ╲                     ▼
       ╲───────────▶ Spec K
```
-/
theorem Scheme.Hom.degree_pullback [IsIntegral X] [IsIntegral Y] (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [IsFinite g] [Surjective g] (M : Y.Modules) [M.IsInvertible] (hample : IsAmple fY M) :
    fX.degree ((Scheme.Modules.pullback g).obj M) =
      g.finrank (genericPoint Y) * fY.degree M :=
  sorry

end AlgebraicGeometry
