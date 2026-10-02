/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs

/-!
# Rigidity

The rigidity lemma says that a morphism `g : X ×_K Y ⟶ Z` of `K`-schemes, with `X` proper,
geometrically connected and geometrically reduced over `K`, `Y` connected and `Z` separated and
locally of finite type over `K`, which contracts a single fibre `X ×_K {y₀}` over a `K`-point
`y₀` to a point, necessarily factors through the second projection. The two auxiliary
propositions leading to it concern the fibres of the morphism `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y`
over `Y`: the locus of `y` whose geometric fibre is contracted to a point is closed, and the
locus of `y` whose fibre has finite image is open.

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

The blueprint uses the rigidity lemma to prove that abelian varieties are commutative. That
corollary is proved instead in `WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic` from
Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, so the chain
below is recorded for its own sake and has no consumer in this repository yet.

## Main definitions

- `AlgebraicGeometry.Scheme.geometricPointOf`: the geometric point
  `Spec κ(y)‾ ⟶ Y` over a point `y : Y`.
- `AlgebraicGeometry.fibreMap`: the base change of `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` along a
  morphism `p : P ⟶ Y`, that is, the fibre of `(g, pr₂)` over `p`.

## Main statements

- `AlgebraicGeometry.isClosed_setOf_subsingleton_image`: the locus of `y : Y` whose geometric
  fibre is contracted to a single point is closed in `Y`.
- `AlgebraicGeometry.eventually_finite_image`: if the fibre over `y₀` has finite image, then so
  does the fibre over every `y` in some open neighbourhood of `y₀`.
- `AlgebraicGeometry.exists_eq_snd_comp`: the rigidity lemma, `g` factors through the second
  projection.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The geometric point `Spec κ(y)‾ ⟶ Y` over a point `y` of a scheme `Y`, where `κ(y)‾` is the
algebraic closure of the residue field `κ(y)`. -/
noncomputable def Scheme.geometricPointOf (Y : Scheme.{u}) (y : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure _))) ≫
    Y.fromSpecResidueField y

variable {K : Type u} [Field K]

/-- The fibre of the morphism `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` over `Y` along a morphism
`p : P ⟶ Y`: the base change `X ×_K Y ×_Y P ⟶ Z ×_K Y ×_Y P` of `(g, pr₂)` along `p`.

For `p = Y.fromSpecResidueField y` this is the fibre map `X_{κ(y)} ⟶ Z_{κ(y)}` over `y`, and
for `p = Y.geometricPointOf y` it is the geometric fibre map over `y`. -/
noncomputable def fibreMap {X Y Z P : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (p : P ⟶ Y) :
    pullback (pullback.snd fX fY) p ⟶ pullback (pullback.snd fZ fY) p :=
  pullback.map _ _ _ _
    (pullback.lift g (pullback.snd fX fY) (by rw [hg, pullback.condition])) (𝟙 P) (𝟙 Y)
    (by simp) (by simp)

/-- Blueprint `sk-prop-av-const-locus`: The locus of constant fibres is closed

Let `X` be a nonempty `K`-scheme proper over `K`, let `Z` be separated over `K`, let `Y` be any
`K`-scheme and let `g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. For `y : Y` let
`g_ȳ : X_{κ(y)‾} ⟶ Z_{κ(y)‾}` be the base change of `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` along the
geometric point `ȳ` over `y`. Then the locus `L = {y ∈ Y | g_ȳ(X_{κ(y)‾}) is a single point}` is
closed in `Y`. Since `X` is nonempty, so is `X_{κ(y)‾}`, and its image is a single point exactly
when it is a subsingleton; this is how `L` is spelled.

Constancy must be tested on the geometric fibre, not on the set-theoretic image of
`X ×_K {y}` in `Z`: for `K` algebraically closed of characteristic `≠ 2`,
`X = Spec K ⊔ Spec K`, `Y = Z = 𝔸¹_K` and `g = (t ↦ t, t ↦ -t)`, that image is one point
exactly for `y` the generic point or `y = 0`, which is not a closed set. -/
theorem isClosed_setOf_subsingleton_image {X Y Z : Scheme.{u}} [Nonempty X]
    (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX]
    [IsSeparated fZ] (g : pullback fX fY ⟶ Z) (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) :
    IsClosed {y : Y |
      (Set.range (fibreMap fX fY fZ g hg (Y.geometricPointOf y)).base).Subsingleton} :=
  sorry

/-- Blueprint `sk-prop-av-image-open`: Finiteness of the image is open in the parameter

Let `X` be proper over `K`, let `Z` be separated and locally of finite type over `K`, let
`g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes and let `y₀ ∈ Y`. For `y : Y` let
`g_y : X_{κ(y)} ⟶ Z_{κ(y)}` be the fibre of `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` over `y`. If the
image of `g_{y₀}` is finite, then the image of `g_y` is finite for every `y` in some open
neighbourhood of `y₀`. -/
theorem eventually_finite_image {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [IsSeparated fZ]
    [LocallyOfFiniteType fZ] (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y₀ : Y)
    (hy₀ : (Set.range (fibreMap fX fY fZ g hg (Y.fromSpecResidueField y₀)).base).Finite) :
    ∃ U : Set Y, IsOpen U ∧ y₀ ∈ U ∧
      ∀ y ∈ U, (Set.range (fibreMap fX fY fZ g hg (Y.fromSpecResidueField y)).base).Finite :=
  sorry

/-- Blueprint `sk-prop-av-rigidity`: The rigidity lemma

Let `X`, `Y`, `Z` be `K`-schemes with `X` proper, geometrically connected and geometrically
reduced over `K`, with `Y` connected and with `Z` separated and locally of finite type over `K`,
and let `g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. If `g (X ×_K {y₀})` is a single point
for some `K`-rational point `y₀ ∈ Y(K)`, then `g` factors through the second projection:
`g = pr₂ ≫ h` for some `h : Y ⟶ Z`, that is, the triangle

```
  pullback fX fY ─── pullback.snd ──▶ Y
             ╲                        │
              ╲  g                    │ h
               ╲                      ▼
                ╲──────────────────▶ Z
```

commutes.

Both geometric hypotheses are needed. For `K = ℝ`, `X = Spec ℂ`, `Y = 𝔸¹_ℝ`, `Z = 𝔸¹_ℂ` and
`g` the identity of `X ×_K Y = 𝔸¹_ℂ`, `X` is connected and geometrically reduced but not
geometrically connected, and `g` does not factor. For `K` imperfect of characteristic `p`,
`a ∈ K ∖ K^p`, `K' = K(a^{1/p})`, `X = Spec K'`, `Y = 𝔸¹_K`, `Z = 𝔸¹_{K'}` and `g` the identity
of `X ×_K Y = 𝔸¹_{K'}`, `X` is geometrically connected and reduced but not geometrically
reduced, and `g` does not factor since `pr₂ : 𝔸¹_{K'} ⟶ 𝔸¹_K` is not a monomorphism.

The proof shows that the locus of `y` whose geometric fibre is contracted is open
(`AlgebraicGeometry.eventually_finite_image`), closed
(`AlgebraicGeometry.isClosed_setOf_subsingleton_image`) and contains `y₀`, hence is all of `Y`;
the factorisation is then constructed locally on `Y` from `Γ(X, 𝒪_X) = K` (which uses that `X`
is proper, geometrically connected and geometrically reduced) and flat base change
`Γ(X ×_K U, 𝒪) = 𝒪(U)` for affine opens `U ⊆ Y`, and glued since `pr₂` is an epimorphism.

The `K`-point `y₀` is given as a section `s : Spec K ⟶ Y` of the structure morphism `fY`, and
the point of the underlying space it names is `s.base (IsLocalRing.closedPoint K)`. -/
theorem exists_eq_snd_comp {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [GeometricallyConnected fX]
    [GeometricallyReduced fX] [ConnectedSpace Y] [IsSeparated fZ] [LocallyOfFiniteType fZ]
    (g : pullback fX fY ⟶ Z) (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (s : Spec (.of K) ⟶ Y)
    (hs : s ≫ fY = 𝟙 _)
    (hy₀ : Set.Subsingleton
      (⇑g '' (⇑(pullback.snd fX fY) ⁻¹' {s.base (IsLocalRing.closedPoint K)}))) :
    ∃ h : Y ⟶ Z, g = pullback.snd fX fY ≫ h :=
  sorry

end AlgebraicGeometry
