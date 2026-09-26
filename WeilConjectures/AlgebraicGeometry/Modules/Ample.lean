/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Ample invertible modules and the Hilbert degree

An invertible `𝒪_X`-module is *very ample* over a field `K` if it is the pullback of `𝒪(1)`
along a closed immersion of `X` into a projective space over `K`, and *ample* if some positive
tensor power of it is very ample. For an ample invertible module `M` on a proper `K`-scheme `X`
of dimension `g`, the function `m ↦ χ(X, M^{⊗ m})` is a numerical polynomial of degree at most
`g`, and the *degree of `X` with respect to `M`* is `g!` times its leading coefficient.

Neither the Serre twisting sheaf `𝒪(1)` nor the Euler characteristic of a coherent sheaf is
available in Mathlib, so `AlgebraicGeometry.IsVeryAmple` and `AlgebraicGeometry.degreeWrt` are
recorded here with `sorry` bodies.

## Main definitions

- `AlgebraicGeometry.IsVeryAmple`, `AlgebraicGeometry.IsAmple`: very ample and ample invertible
  modules on a scheme over a field.
- `AlgebraicGeometry.degreeWrt`: the degree of a proper scheme with respect to an ample
  invertible module.

## Main statements

- `AlgebraicGeometry.degreeWrt_pos_of_isAmple`: an ample invertible module on a proper curve
  has positive degree.
- `AlgebraicGeometry.degreeWrt_pullback`: the degree multiplies by the degree of the morphism
  under pullback along a finite surjective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- An invertible `𝒪_X`-module is *very ample* over `K` if it is the pullback of `𝒪(1)` along a
closed immersion of `X` into a projective space `ℙ^N_K`.

The Serre twisting sheaf is not available in Mathlib, so this is a placeholder. -/
-- TODO(unify): sk-def-av-ample-degree
def IsVeryAmple (f : X ⟶ Spec (.of K)) (M : X.Modules) : Prop := sorry

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An invertible `𝒪_X`-module is *ample* if some positive tensor power of it is very ample. -/
def IsAmple (f : X ⟶ Spec (.of K)) (M : X.Modules) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ IsVeryAmple f (M.tensorPow m)

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

The degree of a proper `K`-scheme `X` of dimension `g` with respect to an ample invertible
`𝒪_X`-module `M`: `g!` times the leading coefficient of the Hilbert polynomial
`m ↦ χ(X, M^{⊗ m})`.

The Euler characteristic of a coherent sheaf is not available in Mathlib, so this is a
placeholder. -/
-- TODO(unify): sk-def-av-ample-degree
noncomputable def degreeWrt (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℤ := sorry

/-- Blueprint `sk-prop-av-ample-positive`: Ample modules on proper curves have positive degree.

Let `K` be algebraically closed, `C` a proper curve over `K` of dimension one (possibly
disconnected) and `L` an ample invertible `𝒪_C`-module. Then `deg L > 0`. -/
theorem degreeWrt_pos_of_isAmple [IsAlgClosed K] (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) (L : X.Modules) (hL : L.IsInvertible)
    (hample : IsAmple f L) :
    0 < degreeWrt f L :=
  sorry

/-- Blueprint `sk-prop-av-deg-pullback`: Degree of a pullback under a finite morphism.

Let `g : X ⟶ Y` be a finite surjective morphism of proper `K`-varieties of the same dimension,
let `M` be an ample invertible `𝒪_Y`-module and let `d = [k(X) : k(Y)]` be the degree of `g`.
Then `deg_{g^*M}(X) = d * deg_M(Y)`. -/
theorem degreeWrt_pullback [IsIntegral X] [IsIntegral Y] (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) [IsProper fX] [IsProper fY] (g : X ⟶ Y) (hg : g ≫ fY = fX)
    [IsFinite g] [Surjective g] (hdim : topologicalKrullDim X = topologicalKrullDim Y)
    (M : Y.Modules) (hM : M.IsInvertible) (hample : IsAmple fY M)
    (d : ℕ) (hd : g.finrank (genericPoint Y) = d) :
    degreeWrt fX ((Scheme.Modules.pullback g).obj M) = d * degreeWrt fY M :=
  sorry

end AlgebraicGeometry
