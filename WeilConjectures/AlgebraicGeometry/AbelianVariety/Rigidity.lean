/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs

/-!
# Rigidity

The rigidity lemma says that a morphism `g : X ×_K Y ⟶ Z` with `X` proper, connected and
reduced over an algebraically closed `K`, `Y` connected and `Z` separated over `K`, which
contracts a single fibre `X ×_K {y₀}` to a point, necessarily contracts *every* fibre, i.e.
factors through the second projection. The two auxiliary propositions leading to it are
topological in nature: the locus of parameters `y` whose fibre is contracted is closed, and the
locus of parameters whose fibre has finite image is open.

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

in which `hg : g ≫ fZ = pullback.fst fX fY ≫ fX` says that `g` is a morphism of `K`-schemes,
and the fibre of the product over a point `y : Y` is the preimage of `{y}` under
`CategoryTheory.Limits.pullback.snd fX fY`.

The blueprint uses the rigidity lemma to prove that abelian varieties are commutative. That
corollary is proved instead in `WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic` from
Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, so the chain
below is recorded for its own sake and has no consumer in this repository yet.

## Main statements

- `AlgebraicGeometry.isClosed_setOf_subsingleton_image`: the locus of parameters `y : Y` whose
  fibre is contracted by `g` to at most one point is closed in `Y`.
- `AlgebraicGeometry.eventually_finite_image`: if the fibre over `y₀` has finite image, then so
  does the fibre over every `y` in some open neighbourhood of `y₀`.
- `AlgebraicGeometry.exists_eq_snd_comp`: the rigidity lemma, `g` factors through the second
  projection.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-const-locus`: The locus of constant fibres is closed

Let `X` be a `K`-scheme proper over `K`, let `Z` be separated over `K`, let `Y` be any
`K`-scheme and let `g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. Then the locus
`L = {y ∈ Y | g (X ×_K {y}) is a single point}` is closed in `Y`. Since "a single point" and
"at most one point" agree on nonempty fibres, `L` is spelled as the subsingleton locus.

This statement is purely topological and, unlike `AlgebraicGeometry.exists_eq_snd_comp`, holds
over an arbitrary field; the blueprint proves it under its standing convention that `K` is
algebraically closed. -/
theorem isClosed_setOf_subsingleton_image {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [IsSeparated fZ]
    (g : pullback fX fY ⟶ Z) (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) :
    IsClosed {y : Y | Set.Subsingleton (⇑g '' (⇑(pullback.snd fX fY) ⁻¹' {y}))} :=
  sorry

/-- Blueprint `sk-prop-av-image-open`: Finiteness of the image is open in the parameter

Let `X` be proper over `K`, let `Z` be separated and locally of finite type over `K`, let
`g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes and let `y₀ ∈ Y`. If the image `g (X ×_K {y₀})`
of the fibre over `y₀` is finite, then `g (X ×_K {y})` is finite for every `y` in some open
neighbourhood of `y₀`.

Like `AlgebraicGeometry.isClosed_setOf_subsingleton_image` this is a topological statement and
holds over an arbitrary field, not only over the algebraically closed field of the blueprint. -/
theorem eventually_finite_image {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [IsSeparated fZ]
    [LocallyOfFiniteType fZ] (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y₀ : Y)
    (hy₀ : (⇑g '' (⇑(pullback.snd fX fY) ⁻¹' {y₀})).Finite) :
    ∃ U : Set Y, IsOpen U ∧ y₀ ∈ U ∧
      ∀ y ∈ U, (⇑g '' (⇑(pullback.snd fX fY) ⁻¹' {y})).Finite :=
  sorry

/-- Blueprint `sk-prop-av-rigidity`: The rigidity lemma

Let `K` be algebraically closed and let `X`, `Y`, `Z` be `K`-schemes with `X` proper, connected
and reduced over `K`, with `Y` connected and with `Z` separated over `K`, and let
`g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. If `g (X ×_K {y₀})` is a single point for some
`K`-rational point `y₀ ∈ Y(K)`, then `g` factors through the second projection: `g = pr₂ ≫ h`
for some `h : Y ⟶ Z`, that is, the triangle

```
  pullback fX fY ─── pullback.snd ──▶ Y
             ╲                        │
              ╲  g                    │ h
               ╲                      ▼
                ╲──────────────────▶ Z
```

commutes.

The hypothesis that `K` be algebraically closed cannot be dropped: over an imperfect `K` of
characteristic `p`, taking `X = Z = Spec K(t^{1/p})`, `Y = 𝔸¹_K` and `g` the first projection
satisfies all the other hypotheses while no factorisation exists. The blueprint's proof uses
algebraic closedness in showing that `X ×_K {y'}` is connected.

The `K`-point `y₀` is given as a section `s : Spec K ⟶ Y` of the structure morphism `fY`, and
the point of the underlying space it names is `s.base (IsLocalRing.closedPoint K)`. -/
theorem exists_eq_snd_comp [IsAlgClosed K] {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [ConnectedSpace X]
    [IsReduced X] [ConnectedSpace Y] [IsSeparated fZ] (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (s : Spec (.of K) ⟶ Y) (hs : s ≫ fY = 𝟙 _)
    (hy₀ : Set.Subsingleton
      (⇑g '' (⇑(pullback.snd fX fY) ⁻¹' {s.base (IsLocalRing.closedPoint K)}))) :
    ∃ h : Y ⟶ Z, g = pullback.snd fX fY ≫ h :=
  sorry

end AlgebraicGeometry
