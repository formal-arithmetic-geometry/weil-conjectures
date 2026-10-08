/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# Ample invertible modules and the Hilbert degree

An `𝒪_X`-module is *very ample* relative to `f : X ⟶ S` if it is the pullback of `𝒪(1)` along
a closed immersion of `X` into a projective space `ℙ(n; S)` over `S`; it is then invertible. An
invertible module on `X` is *ample* relative to `f : X ⟶ S` if some positive tensor power of it
is very ample relative to `f`; both notions make sense over an arbitrary base `S`, and over a
field they are the usual very ample and ample modules on a `K`-scheme.
For an ample invertible module `M` on a proper `K`-scheme `X` of dimension `g`, the function
`m ↦ χ(X, M^{⊗ m})` is a numerical polynomial of degree at most `g`, and the *degree of `X` with
respect to `M`* is `g!` times its leading coefficient.

`AlgebraicGeometry.IsVeryAmple` and `AlgebraicGeometry.IsAmple` are built on the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist`. The degree `AlgebraicGeometry.Scheme.Hom.degree` is
the `g`-th forward difference `fwdDiff` at `0` of the Hilbert function `m ↦ χ(X, M^{⊗ m})`, with
the Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar`; it is `g!` times the
leading coefficient whenever that function is a numerical polynomial of degree at most `g`
(`Polynomial.fwdDiff_iter_degree_eq_factorial`).

## Main definitions

- `AlgebraicGeometry.IsVeryAmple`, `AlgebraicGeometry.IsAmple`: very ample and ample modules
  relative to a morphism `f : X ⟶ S`.
- `AlgebraicGeometry.Scheme.Hom.hilbertFunction`: the Hilbert function `m ↦ χ(X, M^{⊗ m})`.
- `AlgebraicGeometry.Scheme.Hom.degree`: the degree of a proper scheme with respect to an ample
  invertible module.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one`: in dimension
  one the degree is the cohomological degree `χ(M) - χ(𝒪_X)`.
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

An invertible `𝒪_X`-module `M` is *ample* relative to `f : X ⟶ S` (or *`f`-ample*, or
*relatively ample*) if some positive tensor power of it is very ample relative to `f`. Over a
field `S = Spec K` this is the usual notion of an ample module on a `K`-scheme.

Like `AlgebraicGeometry.IsVeryAmple`, this is the "projective" variant of the notion: for a
proper `f` over an affine base it agrees with relative ampleness in the sense of EGA II (4.6.1)
and Stacks `01VG`, by Stacks `0B45`, while over a general base it asks in addition that the
embedding of some tensor power be into a trivial projective space `ℙ(n; S)`. -/
def IsAmple {S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∃ m : ℕ, 0 < m ∧ IsVeryAmple f (M.tensorPow m)

/-- The Hilbert function `m ↦ χ(X, M^{⊗ m})` of an `𝒪_X`-module `M` on a `K`-scheme `X`, with
the Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar` over `K`. -/
noncomputable def Scheme.Hom.hilbertFunction (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℕ → ℤ :=
  letI : X.Over (Spec (.of K)) := ⟨f⟩
  fun m ↦ Scheme.Modules.eulerChar K (M.tensorPow m)

open scoped fwdDiff in
/-- Blueprint `sk-def-av-ample-degree`: Ample modules and the Hilbert degree.

The degree of a `K`-scheme `X` of dimension `g` with respect to an `𝒪_X`-module `M`: the `g`-th
forward difference at `0` of the Hilbert function `m ↦ χ(X, M^{⊗ m})`. When the Hilbert
function is a numerical polynomial of degree at most `g`, as it is for `X` proper and `M` ample
invertible, this equals `g!` times its coefficient of `m^g`. Here `g` is the topological Krull
dimension of `X`, read as `0` if `X` is empty or infinite-dimensional.

The value is meaningful only for `f` proper and `M` coherent: otherwise the Euler
characteristics involved may be junk values. -/
noncomputable def Scheme.Hom.degree (f : X ⟶ Spec (.of K)) (M : X.Modules) : ℤ :=
  Δ_[1]^[((topologicalKrullDim X).unbotD 0).toNat] (f.hilbertFunction M) 0

/-- The degree as an explicit alternating sum of Euler characteristics:
`∑_{i=0}^{g} (-1)^(g-i) (g choose i) χ(X, M^{⊗ i})`. -/
lemma Scheme.Hom.degree_eq_sum (f : X ⟶ Spec (.of K)) (M : X.Modules) :
    f.degree M = ∑ i ∈ Finset.range (((topologicalKrullDim X).unbotD 0).toNat + 1),
      ((-1 : ℤ) ^ (((topologicalKrullDim X).unbotD 0).toNat - i) *
        (((topologicalKrullDim X).unbotD 0).toNat.choose i : ℤ)) • f.hilbertFunction M i := by
  rw [degree, fwdDiff_iter_eq_sum_shift]
  simp

/-- On a `K`-scheme of dimension one, the degree with respect to `M` is the cohomological
degree `χ(M) - χ(𝒪_X)` of `AlgebraicGeometry.Scheme.Modules.degree`. -/
lemma Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one (f : X ⟶ Spec (.of K))
    (h : topologicalKrullDim X = 1) (M : X.Modules) :
    letI : X.Over (Spec (.of K)) := ⟨f⟩
    f.degree M = Scheme.Modules.degree K M := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  have hg : ((topologicalKrullDim X).unbotD 0).toNat = 1 := by
    rw [h]
    rfl
  rw [degree, hg, Function.iterate_one, fwdDiff, zero_add, Scheme.Modules.degree]
  simp only [hilbertFunction, Scheme.Modules.tensorPow_zero]
  rw [Scheme.Modules.tensorPow_succ, Scheme.Modules.tensorPow_zero,
    Scheme.Modules.eulerChar_congr K (MonoidalCategory.rightUnitor M)]
  rfl

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
