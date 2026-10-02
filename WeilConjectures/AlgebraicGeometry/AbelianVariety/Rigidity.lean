/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField

/-!
# Rigidity

The rigidity lemma says that a morphism `g : X ×_K Y ⟶ Z` of `K`-schemes, with `X` proper,
geometrically connected and geometrically reduced over `K`, `Y` connected and `Z` separated over
`K`, which contracts a single fibre `X ×_K {y₀}` to a point, necessarily factors through the
second projection. This file also records two propositions on the fibres of the morphism
`(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` over `Y`: the locus of `y` whose geometric fibre is contracted to
a point is closed, and the locus of `y` whose fibre has finite image is open. The second one is
independent of the rigidity lemma.

All three statements are set in the commutative square

```
  pullback fX fY ───── pullback.snd ─────▶ Y
        │        ╲                         │
        │         ╲  g                     │ fY
 pullback.fst      ╲                       │
        │           ╲                      │
        ▼            ▼                     ▼
        X ─── fX ──▶ Spec K ◀─── fZ ────── Z
```

in which `hg : g ≫ fZ = pullback.fst fX fY ≫ fX` says that `g` is a morphism of `K`-schemes.
The fibres of `(g, pr₂) = pullback.lift g (pullback.snd fX fY) _` over `Y` are spelled with
`AlgebraicGeometry.Scheme.Hom.fiberMap`.

The blueprint uses the rigidity lemma to prove that abelian varieties are commutative. That
corollary is proved instead in `WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic` from
Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, so the results
below are recorded for their own sake and have no consumer in this repository yet.

## Main statements

- `AlgebraicGeometry.isClosed_setOf_subsingleton_image`: the locus of `y : Y` whose geometric
  fibre is contracted to a single point is closed in `Y`.
- `AlgebraicGeometry.eventually_finite_image`: if the fibre over `y₀` has finite image, then so
  does the fibre over every `y` near `y₀`.
- `AlgebraicGeometry.exists_eq_snd_comp`: the rigidity lemma, `g` factors through the second
  projection.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-const-locus`: The locus of constant fibres is closed

Let `X` be a `K`-scheme proper over `K`, let `Z` be separated over `K`, let `Y` be any
`K`-scheme and let `g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. For `y : Y` let
`g_ȳ : X_{κ(y)‾} ⟶ Z_{κ(y)‾}` be the base change of `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` along the
geometric point `ȳ` over `y`. Then the locus `L = {y ∈ Y | g_ȳ(X_{κ(y)‾}) is a subsingleton}` is
closed in `Y`. For nonempty `X` the image of `g_ȳ` is a subsingleton exactly when it is a single
point.

Constancy must be tested on the geometric fibre, not on the set-theoretic image of
`X ×_K {y}` in `Z`: for `K` algebraically closed of characteristic `≠ 2`,
`X = Spec K ⊔ Spec K`, `Y = Z = 𝔸¹_K` and `g = (t ↦ t, t ↦ -t)`, that image is one point
exactly for `y` the generic point or `y = 0`, which is not a closed set. -/
theorem isClosed_setOf_subsingleton_image {X Y Z : Scheme.{u}}
    (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX]
    [IsSeparated fZ] (g : pullback fX fY ⟶ Z) (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) :
    IsClosed {y : Y | (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecAlgebraicClosureResidueField y)).base).Subsingleton} :=
  sorry

/-- Blueprint `sk-prop-av-image-open`: Finiteness of the image is open in the parameter

Let `X` be proper over `K`, let `Z` be separated and locally of finite type over `K`, let
`g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes and let `y₀ ∈ Y`. For `y : Y` let
`g_y : X_{κ(y)} ⟶ Z_{κ(y)}` be the fibre of `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` over `y`. If the
image of `g_{y₀}` is finite, then the image of `g_y` is finite for every `y` in some open
neighbourhood of `y₀`.

The rigidity lemma `AlgebraicGeometry.exists_eq_snd_comp` does not depend on this result. -/
theorem eventually_finite_image {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [IsSeparated fZ]
    [LocallyOfFiniteType fZ] (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y₀ : Y)
    (hy₀ : (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecResidueField y₀)).base).Finite) :
    ∀ᶠ y in 𝓝 y₀, (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecResidueField y)).base).Finite :=
  sorry

/-- Blueprint `sk-prop-av-rigidity`: The rigidity lemma

Let `X`, `Y`, `Z` be `K`-schemes with `X` proper, geometrically connected and geometrically
reduced over `K`, with `Y` connected and with `Z` separated over `K`, and let
`g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. If `g (X ×_K {y₀})` is a single point for some
point `y₀ ∈ Y`, then `g` factors through the second projection: `g = pr₂ ≫ h` for some
`h : Y ⟶ Z`, that is, the triangle

```
  pullback fX fY ─── pullback.snd ──▶ Y
             ╲                        │
              ╲  g                    │ h
               ╲                      ▼
                ╲──────────────────▶ Z
```

commutes. The set `g (X ×_K {y₀})` is spelled as the range of the restriction of `g` to the
scheme-theoretic fibre of `pr₂` over `y₀`; the point `y₀` need not be `K`-rational.

Neither geometric hypothesis on `X` can be dropped on its own. For `K = ℝ`, `X = Spec ℂ`,
`Y = 𝔸¹_ℝ`, `Z = 𝔸¹_ℂ` and `g` the identity of `X ×_K Y = 𝔸¹_ℂ`, `X` is connected and
geometrically reduced but not geometrically connected, and `g` does not factor. For `K`
imperfect of characteristic `p`, `a ∈ K ∖ K^p`, `K' = K(a^{1/p})`, `X = Spec K'`, `Y = 𝔸¹_K`,
`Z = 𝔸¹_{K'}` and `g` the identity of `X ×_K Y = 𝔸¹_{K'}`, `X` is geometrically connected and
reduced but not geometrically reduced, and `g` does not factor since `pr₂ : 𝔸¹_{K'} ⟶ 𝔸¹_K` is
not a monomorphism. In both examples `Γ(X, 𝒪_X) ≠ K`. -/
theorem exists_eq_snd_comp {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [GeometricallyConnected fX]
    [GeometricallyReduced fX] [ConnectedSpace Y] [IsSeparated fZ]
    (g : pullback fX fY ⟶ Z) (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y₀ : Y)
    (hy₀ : (Set.range ((pullback.snd fX fY).fiberι y₀ ≫ g).base).Subsingleton) :
    ∃ h : Y ⟶ Z, g = pullback.snd fX fY ≫ h :=
  -- Proof sketch (Mumford, Abelian Varieties §4). Let `L'` be the set of `y` with
  -- `g (X ×_K {y})` a single point. For `y ∈ L'` and an affine open `V` around that point,
  -- `Y ∖ pr₂ (g⁻¹ (Z ∖ V))` is an open neighbourhood of `y` since `pr₂` is closed. On an
  -- affine open `U` inside it, `Γ(X ×_K U, 𝒪) = 𝒪(U)` (flat base change and `Γ(X, 𝒪_X) = K`)
  -- gives `g = pr₂ ≫ h_U` on `X ×_K U`. So `L'` is open and equals the geometric locus of
  -- `isClosed_setOf_subsingleton_image`, which is closed; as `Y` is connected, `L' = Y`, and
  -- the `h_U` glue since `pr₂` is an epimorphism.
  sorry

end AlgebraicGeometry
