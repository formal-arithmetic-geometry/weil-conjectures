/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField

/-!
# Rigidity

The rigidity lemma says that a morphism `g : X ×_S Y ⟶ Z` of `S`-schemes, with `X` proper, flat
and of finite presentation over `S` with geometrically connected and geometrically reduced
fibres, `Y` connected and `Z` separated over `S`, which contracts a single fibre `X ×_S {y₀}` to
a point, necessarily factors through the second projection. This file also records two
propositions on the fibres of the morphism `(g, pr₂) : X ×_S Y ⟶ Z ×_S Y` over `Y`: the locus
of `y` whose geometric fibre is contracted to a point is closed, and the locus of `y` whose fibre
has finite image is open. The second one is independent of the rigidity lemma.

All three statements are set in the commutative square

```
  pullback fX fY ───── pullback.snd ─────▶ Y
        │        ╲                         │
        │         ╲  g                     │ fY
 pullback.fst      ╲                       │
        │           ╲                      │
        ▼            ▼                     ▼
        X ─── fX ──▶ S ◀───── fZ ───────── Z
```

in which `hg : g ≫ fZ = pullback.fst fX fY ≫ fX` says that `g` is a morphism of `S`-schemes.
The fibres of `(g, pr₂) = pullback.lift g (pullback.snd fX fY) _` over `Y` are spelled with
`AlgebraicGeometry.Scheme.Hom.fiberMap`.

The blueprint states all three results over a field `K`, that is, for `S = Spec K`. Over a
field every morphism is flat, and a morphism locally of finite type is locally of finite
presentation, so the hypotheses `Flat fX` and `LocallyOfFinitePresentation fX` below only
matter over a general base; see the docstrings for why they cannot be dropped there. The
hypotheses of the rigidity lemma are exactly those of Stacks Project Tag 0E0L, which gives
`𝒪_S = fX_* 𝒪_X` universally, the form in which Mumford states the lemma over a general base
(Geometric Invariant Theory, Proposition 6.1).

The blueprint uses the rigidity lemma to prove that abelian varieties are commutative. That
corollary is stated in `WeilConjectures.AlgebraicGeometry.AbelianScheme.Basic` for abelian
schemes over any base, where the rigidity lemma below applies since the structure morphism of
an abelian scheme is proper and smooth with geometrically connected fibres; over a field it is
also Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`.

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

variable {S X Y Z : Scheme.{u}}

/-- Blueprint `sk-prop-av-const-locus`: The locus of constant fibres is closed

Let `X` be proper, flat and of finite presentation over `S`, let `Z` be separated over `S`, let
`Y` be any `S`-scheme and let `g : X ×_S Y ⟶ Z` be a morphism of `S`-schemes. For `y : Y` let
`g_ȳ : X_{κ(y)‾} ⟶ Z_{κ(y)‾}` be the base change of `(g, pr₂) : X ×_S Y ⟶ Z ×_S Y` along the
geometric point `ȳ` over `y`. Then the locus `L = {y ∈ Y | g_ȳ(X_{κ(y)‾}) is a subsingleton}` is
closed in `Y`. For `X` with nonempty fibres the image of `g_ȳ` is a subsingleton exactly when it
is a single point.

Constancy must be tested on the geometric fibre, not on the set-theoretic image of
`X ×_S {y}` in `Z`: for `S = Spec K` with `K` algebraically closed of characteristic `≠ 2`,
`X = Spec K ⊔ Spec K`, `Y = Z = 𝔸¹_K` and `g = (t ↦ t, t ↦ -t)`, that image is one point
exactly for `y` the generic point or `y = 0`, which is not a closed set.

Over a field flatness and finite presentation are automatic, but over a general base neither
can be dropped. For `X = Bl₀ 𝔸² ⟶ S = 𝔸²`, `Y = S`, `Z = ℙ¹ × S` and `g = (π, pr)` with `π` the
projection of the blow-up to `ℙ¹`, the fibre over `y` is contracted exactly for `y ≠ 0`, an open
set; here `X ⟶ S` is proper but not flat. For `S = Spec A` with `A = ∏_ℕ 𝔽₂`, `I ⊆ A` an ideal
that is not finitely generated, `V = Spec A/I`, `X = Z = V ⊔ V ⟶ S`, `Y = S` and `g` the
identity, the fibre over `y` is contracted exactly for `y ∉ V`, again an open set that is not
closed; here `X ⟶ S` is finite and flat but not of finite presentation. -/
theorem isClosed_setOf_subsingleton_image (fX : X ⟶ S) (fY : Y ⟶ S) (fZ : Z ⟶ S) [IsProper fX]
    [Flat fX] [LocallyOfFinitePresentation fX] [IsSeparated fZ] (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) :
    IsClosed {y : Y | (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecAlgebraicClosureResidueField y)).base).Subsingleton} :=
  sorry

/-- Blueprint `sk-prop-av-image-open`: Finiteness of the image is open in the parameter

Let `X` be proper over `S`, let `Z` be separated and locally of finite type over `S`, let
`g : X ×_S Y ⟶ Z` be a morphism of `S`-schemes and let `y₀ ∈ Y`. For `y : Y` let
`g_y : X_{κ(y)} ⟶ Z_{κ(y)}` be the fibre of `(g, pr₂) : X ×_S Y ⟶ Z ×_S Y` over `y`. If the
image of `g_{y₀}` is finite, then the image of `g_y` is finite for every `y` in some open
neighbourhood of `y₀`.

The rigidity lemma `AlgebraicGeometry.exists_eq_snd_comp` does not depend on this result. -/
theorem eventually_finite_image (fX : X ⟶ S) (fY : Y ⟶ S) (fZ : Z ⟶ S) [IsProper fX]
    [IsSeparated fZ] [LocallyOfFiniteType fZ] (g : pullback fX fY ⟶ Z)
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

Let `X`, `Y`, `Z` be `S`-schemes with `X` proper, flat and of finite presentation over `S` with
geometrically connected and geometrically reduced fibres, with `Y` connected and with `Z`
separated over `S`, and let `g : X ×_S Y ⟶ Z` be a morphism of `S`-schemes. If `g (X ×_S {y₀})`
is a single point for some point `y₀ ∈ Y`, then `g` factors through the second projection:
`g = pr₂ ≫ h` for some `h : Y ⟶ Z`, that is, the triangle

```
  pullback fX fY ─── pullback.snd ──▶ Y
             ╲                        │
              ╲  g                    │ h
               ╲                      ▼
                ╲──────────────────▶ Z
```

commutes. The set `g (X ×_S {y₀})` is spelled as the range of the restriction of `g` to the
scheme-theoretic fibre of `pr₂` over `y₀`; the point `y₀` need not be a section.

The hypotheses on `X` are those of Stacks Project Tag 0E0L, which gives `𝒪_S = fX_* 𝒪_X`
universally, that is, `𝒪_Y = (pr₂)_* 𝒪_{X ×_S Y}` for every `S`-scheme `Y`; this is the form of
the hypothesis in Mumford, Geometric Invariant Theory, Proposition 6.1. Over a field `S = Spec K`
flatness and finite presentation are automatic, and neither geometric hypothesis on `X` can be
dropped on its own. For `K = ℝ`, `X = Spec ℂ`, `Y = 𝔸¹_ℝ`, `Z = 𝔸¹_ℂ` and `g` the identity of
`X ×_K Y = 𝔸¹_ℂ`, `X` is connected and geometrically reduced but not geometrically connected,
and `g` does not factor. For `K` imperfect of characteristic `p`, `a ∈ K ∖ K^p`,
`K' = K(a^{1/p})`, `X = Spec K'`, `Y = 𝔸¹_K`, `Z = 𝔸¹_{K'}` and `g` the identity of
`X ×_K Y = 𝔸¹_{K'}`, `X` is geometrically connected and reduced but not geometrically reduced,
and `g` does not factor since `pr₂ : 𝔸¹_{K'} ⟶ 𝔸¹_K` is not a monomorphism. In both examples
`Γ(X, 𝒪_X) ≠ K`. -/
theorem exists_eq_snd_comp (fX : X ⟶ S) (fY : Y ⟶ S) (fZ : Z ⟶ S) [IsProper fX] [Flat fX]
    [LocallyOfFinitePresentation fX] [GeometricallyConnected fX] [GeometricallyReduced fX]
    [ConnectedSpace Y] [IsSeparated fZ] (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y₀ : Y)
    (hy₀ : (Set.range ((pullback.snd fX fY).fiberι y₀ ≫ g).base).Subsingleton) :
    ∃ h : Y ⟶ Z, g = pullback.snd fX fY ≫ h :=
  -- Proof sketch (Mumford, Geometric Invariant Theory, Proposition 6.1). Let `L'` be the set
  -- of `y` with `g (X ×_S {y})` a single point. For `y ∈ L'` and an affine open `V` around
  -- that point, `Y ∖ pr₂ (g⁻¹ (Z ∖ V))` is an open neighbourhood of `y` since `pr₂` is
  -- closed. On an affine open `U` inside it, `Γ(X ×_S U, 𝒪) = 𝒪(U)` (Stacks Project Tag 0E0L
  -- applied to the base change `X ×_S U ⟶ U`) gives `g = pr₂ ≫ h_U` on `X ×_S U`. So `L'` is
  -- open and equals the geometric locus of `isClosed_setOf_subsingleton_image`, which is
  -- closed; as `Y` is connected, `L' = Y`, and the `h_U` glue since `pr₂` is an epimorphism.
  sorry

end AlgebraicGeometry
