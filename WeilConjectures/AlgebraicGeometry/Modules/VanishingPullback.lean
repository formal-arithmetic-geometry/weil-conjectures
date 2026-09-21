/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial

/-!
# Vanishing of a section of a line bundle is compatible with pullback

A global section `s` of a sheaf of `𝒪ₓ`-modules `F` on a scheme `X` *vanishes* at a point `x`
when its germ at `x` lies in `𝔪ₓ Fₓ` (`AlgebraicGeometry.Scheme.Modules.VanishesAt`). This file
proves that for an **invertible** sheaf of modules this notion is compatible with pullback: for
`a : X ⟶ Y` and `s` a global section of an invertible `𝒪ᵧ`-module `L`, the pullback `a^* s`
vanishes at `x` exactly when `s` vanishes at `a x`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.vanishesAt_sectionsPullback_iff`: **vanishing of a section
  of a line bundle is compatible with pullback.**

## Blueprint

The theorem below is `lem:deg-vanishing-pullback` of
`curve_estimates/28_degree_of_the_isogeny.tex`. It supplies a step which the informal proof of
`lem:deg-general-hyperplane` there leaves implicit: the hyperplane is chosen on `𝐏ᴺ`, by a
condition in the residue field at `i(xₗ)`, and the resulting section of `L = i^* 𝒪(1)` has to
be recognised as non-vanishing at `xₗ`. The `## TODO` below is recorded in the blueprint as
`rem:deg-vanishing-pullback-general`.

## Implementation notes

The proof has three ingredients, all of them general statements living in the Mathlib mirror
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.

* **Open immersions.** Pulling back along an open immersion does not change stalks, so
  vanishing is unchanged. This is
  `AlgebraicGeometry.Scheme.Modules.vanishesAt_sectionsPullback_iff_of_isOpenImmersion`.
* **A globally trivialised sheaf.** If `L` is trivialised by a global section `t`, every global
  section of `L` is `g • t` for a unique global function `g`, and it vanishes exactly outside
  the basic open subset of `g`; multiplication by `t` pulls back to multiplication by `a^* t`,
  so the same description holds upstairs. This is
  `AlgebraicGeometry.Scheme.Modules.vanishesAt_sectionsPullback_iff_of_isIso_homOfSectionTop`.
* **Localisation.** An invertible sheaf is trivialised by a global section after restriction to
  some open `W` around `a x` (`SheafOfModules.Invertible.exists_isIso_homOfSectionTop`), and the
  commuting square of the theorem below reads the pullback along `a`, localised at `x`, as a
  pullback of a trivialised sheaf followed by two open immersions. The two readings are matched
  by `AlgebraicGeometry.Scheme.Modules.vanishesAt_sectionsPullback_triangle_iff`.

## TODO

Invertibility of `L` is not needed mathematically: the statement holds for an arbitrary sheaf
of modules, because `(a^* M)ₓ ≅ 𝒪_{X, x} ⊗_{𝒪_{Y, a x}} M_{a x}` and a field extension is
faithfully flat. The missing input is that base-change comparison for stalks — equivalently
`AlgebraicGeometry.Scheme.Modules.fiberPullbackIso` without its `[IsIso (u.residueFieldMap x)]`
hypothesis, together with the identification of
`AlgebraicGeometry.Scheme.Modules.VanishesAt` with the vanishing of the fibre. Both are already
recorded as missing in `WeilConjectures.AlgebraicGeometry.Modules.Vanishing` and
`WeilConjectures.AlgebraicGeometry.MiracleFlatness`. With them the theorem below becomes a
corollary for every `M : Y.Modules`, and its easy direction holds for every morphism of sheaves
of modules.
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **Vanishing of a section of a line bundle is compatible with pullback**: a global section
`s` of an invertible sheaf of modules `L` on `Y` vanishes at `a x` exactly when its pullback
along `a : X ⟶ Y` vanishes at `x`.

The proof localises over an open `W ∋ a x` on which `L` is trivialised, along the commuting
square

```text
  a ⁻¹ᵁ W  ──── a ∣_ W ────▶  W
     │                        │
 (a ⁻¹ᵁ W).ι                 W.ι
     │                        │
     ▼                        ▼
     X    ─────── a ───────▶  Y
```
-/
theorem vanishesAt_sectionsPullback_iff (a : X ⟶ Y) {L : Y.Modules} (hL : L.Invertible)
    (s : Γ(L, ⊤)) (x : X) :
    ((pullback a).obj L).VanishesAt (sectionsPullback a L s) x ↔ L.VanishesAt s (a.base x) := by
  obtain ⟨W, hW, t, ht⟩ := hL.exists_isIso_homOfSectionTop (a.base x)
  have hxW : x ∈ a ⁻¹ᵁ W := hW
  have hu : (a ∣_ W) ≫ W.ι = (a ⁻¹ᵁ W).ι ≫ a := morphismRestrict_ι a W
  -- restrict to the open subscheme `a ⁻¹ᵁ W` of `X`
  have h1 := (vanishesAt_sectionsPullback_iff_of_isOpenImmersion (a ⁻¹ᵁ W).ι
    ((pullback a).obj L) (sectionsPullback a L s) ⟨x, hxW⟩).symm
  -- read the two-step pullback along `(a ⁻¹ᵁ W).ι ≫ a` in two ways: first as a pullback
  -- along `a` followed by a pullback along the open immersion `(a ⁻¹ᵁ W).ι` …
  have h2 := vanishesAt_sectionsPullback_triangle_iff
    (rfl : (a ⁻¹ᵁ W).ι ≫ a = (a ⁻¹ᵁ W).ι ≫ a) L s ⟨x, hxW⟩
  -- … and then as a pullback to the trivialising open `W` followed by a pullback along `a ∣_ W`
  have h3 := vanishesAt_sectionsPullback_triangle_iff hu L s ⟨x, hxW⟩
  refine h1.trans (h2.trans (h3.symm.trans ?_))
  rw [vanishesAt_sectionsPullback_iff_of_isIso_homOfSectionTop (a ∣_ W) t,
    vanishesAt_sectionsPullback_iff_of_isOpenImmersion W.ι L s]
  simp

end AlgebraicGeometry.Scheme.Modules
