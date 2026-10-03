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
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# Ample invertible modules and the Hilbert degree

An `𝒪_X`-module is *very ample* relative to `f : X ⟶ S` if it is the pullback of `𝒪(1)` along
a closed immersion of `X` into a projective space `ℙ(n; S)` over `S`; it is then invertible. An
invertible module on a `K`-scheme is *ample* if some positive tensor power of it is very ample.
For an ample invertible module `M` on a proper `K`-scheme `X` of dimension `g`, the function
`m ↦ χ(X, M^{⊗ m})` is a numerical polynomial of degree at most `g`, and the *degree of `X` with
respect to `M`* is `g!` times its leading coefficient.

`AlgebraicGeometry.IsVeryAmple` and `AlgebraicGeometry.IsAmple` are built on the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist`. The degree `AlgebraicGeometry.Scheme.Hom.degree` is
the `g`-th forward difference at `0` of `m ↦ χ(X, M^{⊗ m})`, with the Euler characteristic
`AlgebraicGeometry.Scheme.Modules.eulerChar`; it is `g!` times the leading coefficient whenever
that function is a numerical polynomial of degree at most `g`.

## Main definitions

- `AlgebraicGeometry.IsVeryAmple`, `AlgebraicGeometry.IsAmple`: very ample and ample modules.
- `AlgebraicGeometry.Scheme.Hom.degree`: the degree of a proper scheme with respect to an ample
  invertible module.

## Main statements

- `AlgebraicGeometry.IsVeryAmple.isInvertible`: a very ample module is invertible.
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

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An `𝒪_X`-module `M` is *very ample* relative to `f : X ⟶ S` if there is a closed immersion
`i : X ⟶ ℙ(n; S)` over `S`, into a projective space with finitely many homogeneous
coordinates, with `i^* 𝒪(1) ≅ M`.

This is the "projective" variant of the notion: Hartshorne (II.5) and EGA II (4.4.2) only ask
for an immersion. The two agree when `f` is proper, since an immersion from a proper
`S`-scheme into the separated `S`-scheme `ℙ(n; S)` is closed, and every use of very ample
modules in the project is for a proper `f`. -/
def IsVeryAmple {S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∃ (n : Type u) (i : X ⟶ ℙ(n; S)), Finite n ∧ IsClosedImmersion i ∧ i ≫ ℙ(n; S) ↘ S = f ∧
    Nonempty (ProjectiveSpace.twistRestrict i 1 ≅ M)

/-- **A very ample module is invertible**, being the pullback of the invertible module
`𝒪(1)`. -/
lemma IsVeryAmple.isInvertible {S : Scheme.{u}} {f : X ⟶ S} {M : X.Modules}
    (h : IsVeryAmple f M) : M.IsInvertible := by
  obtain ⟨n, i, -, -, -, ⟨e⟩⟩ := h
  exact Scheme.Modules.IsInvertible.of_iso e

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

An invertible `𝒪_X`-module is *ample* if some positive tensor power of it is very ample. -/
def IsAmple (f : X ⟶ Spec (.of K)) (M : X.Modules) : Prop :=
  ∃ m : ℕ, 0 < m ∧ IsVeryAmple f (M.tensorPow m)

/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

The degree of a proper `K`-scheme `X` of dimension `g` with respect to an ample invertible
`𝒪_X`-module `M`: `g!` times the leading coefficient of the Hilbert polynomial
`m ↦ χ(X, M^{⊗ m})`.

It is defined as the `g`-th forward difference at `0` of the Hilbert function,
`∑_{i=0}^{g} (-1)^(g-i) (g choose i) χ(X, M^{⊗ i})`. Whenever the Hilbert function is a numerical
polynomial of degree at most `g` this is `g!` times its coefficient of `m^g`, which is the
blueprint's definition; the definition itself needs no proof that it is one. Here `g` is the
topological Krull dimension of `X`, read as `0` if `X` is empty or infinite-dimensional. -/
-- TODO(unify): sk-def-av-ample-degree
noncomputable def Scheme.Hom.degree (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℤ :=
  letI : X.Over (Spec (.of K)) := ⟨f⟩
  let g : ℕ := ((topologicalKrullDim X).unbotD 0).toNat
  ∑ i ∈ Finset.range (g + 1),
    (-1) ^ (g - i) * (g.choose i : ℤ) * Scheme.Modules.eulerChar K (M.tensorPow i)

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
