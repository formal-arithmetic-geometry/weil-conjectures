/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ThickeningFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# The ideal of a flat infinitesimal thickening is free over the zeroth neighbourhood

Let `f : W ⟶ T` be a **flat** morphism of schemes, let `t` be a point of `T`, write
`Wₘ := W ×_T Tₘ` for the base change of `f` along the `m`-th infinitesimal neighbourhood of
`t`, let `Iₙ` be the thickening ideal of `Wₙ ↪ W_{n+1}` and let `i₀ : W₀ ↪ W_{n+1}` be the
closed immersion of the zeroth infinitesimal neighbourhood.

This file proves what `WeilConjectures.AlgebraicGeometry.ThickeningFree` leaves open: the
comparison morphism

```
  Φ : (i₀)_* (𝒪_{W₀} ^ ι) ⟶ Iₙ
```

of `AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal` **is an isomorphism** when the
family `m : ι → Γ(Iₙ, ⊤)` lies over a `κ(t)`-basis of `𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2)`. So the
thickening ideal of a flat infinitesimal thickening is, as a sheaf of modules, free of finite
rank on the zeroth infinitesimal neighbourhood.

Writing `B = 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 2)` and `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))`, the whole
content is the verification of the two stalkwise hypotheses of
`AlgebraicGeometry.Scheme.IdealSheafData.isIso_pushforwardFreeDesc` at a point `x` of
`W_{n+1}`, both of which are statements about ideals of the local ring `S = 𝒪_{W_{n+1}, x}`
extended from `B` along `AlgebraicGeometry.Scheme.infinitesimalRingToStalk`:

* **spanning.** The stalk of `Iₙ` is the extension `K S`
  (`AlgebraicGeometry.Scheme.stalkIdeal_thickeningIdeal`), and `K` is spanned by the `e j`, so
  `K S` is spanned by their images. No flatness is needed, and the inclusion is an equality.
* **relations.** The stalk of the kernel ideal sheaf of `i₀` is the extension `𝔪_B S`
  (`AlgebraicGeometry.Scheme.stalkIdeal_ker_infinitesimalBaseChangeMapZero`), and the
  relations between the `e j` over `B` all have their coefficients in `𝔪_B`. Flatness of
  `S` over `B` (`AlgebraicGeometry.Scheme.flat_infinitesimalRingToStalk`) transports
  that to `S` by the equational criterion, in the form
  `Module.Flat.mem_ideal_map_of_sum_mul_eq_zero`.

Flatness of `f` therefore enters exactly once, and only through the second hypothesis.

## Main results

- `AlgebraicGeometry.Scheme.isIso_pushforwardFreeToThickeningIdeal` — the comparison morphism
  attached to a family of global sections lying over a residue-field basis of `K` is an
  isomorphism.
- `AlgebraicGeometry.Scheme.exists_isIso_pushforwardFreeToThickeningIdeal` — such a family
  exists as soon as `K` is finitely generated; this is the form to feed to
  `WeilConjectures.AlgebraicGeometry.Cohomology.ThickeningFree`, whose results take the
  `IsIso` as an instance hypothesis.
- `AlgebraicGeometry.Scheme.exists_nonempty_iso_thickeningIdeal_toModules` — the resulting
  isomorphism `(i₀)_* (𝒪_{W₀} ^ ι) ≅ Iₙ` for a finite index type `ι`, which is the statement
  that `Iₙ` is free of finite rank on the zeroth neighbourhood.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {T W : Scheme.{u}} (f : W ⟶ T) (t : T) (n : ℕ)

/-- **The comparison morphism `(i₀)_* (𝒪_{W₀} ^ ι) ⟶ Iₙ` is an isomorphism** when the global
sections `m j` of the thickening ideal lie over a family `e : ι → B` spanning
`K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` all of whose relations have coefficients in `𝔪_B`,
that is, over a `κ(t)`-basis of `K`, and when `f` is flat.

The two hypotheses `hspan` and `hind` are exactly what
`AlgebraicGeometry.Scheme.exists_span_eq_and_forall_toModulesι_app_eq` produces, together
with `hm`; see `AlgebraicGeometry.Scheme.exists_isIso_pushforwardFreeToThickeningIdeal`. -/
theorem isIso_pushforwardFreeToThickeningIdeal [Flat f] {ι : Type u} [Fintype ι]
    {e : ι → T.infinitesimalRing t (n + 1)}
    (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤))
    (hspan : Ideal.span (Set.range e) =
      RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom)
    (hind : ∀ c : ι → T.infinitesimalRing t (n + 1), ∑ i, c i * e i = 0 →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal (T.infinitesimalRing t (n + 1)))
    (hm : ∀ j, (thickeningIdeal f t n).toModulesι.app ⊤ (m j) =
      infinitesimalRingToΓ f t (n + 1) (e j)) :
    IsIso (pushforwardFreeToThickeningIdeal f t n m) := by
  -- the germ of `m j` at `x` is the image of `e j` in the stalk
  have hgerm : ∀ x : infinitesimalBaseChange f t (n + 1), ∀ j,
      (infinitesimalBaseChange f t (n + 1)).presheaf.germ ⊤ x trivial
          ((thickeningIdeal f t n).toModulesι.app ⊤ (m j)) =
        infinitesimalRingToStalk f t (n + 1) x (e j) := fun x j ↦ by
    rw [hm j, germ_infinitesimalRingToΓ]
  refine IdealSheafData.isIso_pushforwardFreeDesc _ _ m (fun x c hc j ↦ ?_) fun x ↦ ?_
  · -- the relations between the `m j` on the stalk have coefficients in `𝔪_B S`
    have := flat_infinitesimalRingToStalk f t (n + 1) x
    algebraize [(infinitesimalRingToStalk f t (n + 1) x).hom]
    rw [stalkIdeal_ker_infinitesimalBaseChangeMapZero]
    exact Module.Flat.mem_ideal_map_of_sum_mul_eq_zero hind
      (by simpa only [hgerm x, RingHom.algebraMap_toAlgebra] using hc) j
  · -- the stalk of `Iₙ` is the extension of `K`, which the `e j` span
    rw [stalkIdeal_thickeningIdeal, ← hspan, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨j, hgerm x j⟩

/-- **The thickening ideal of a flat infinitesimal thickening is free of finite rank on the
zeroth infinitesimal neighbourhood**: there is a finite index type `ι` and a family `m` of
global sections of `Iₙ` for which the comparison morphism
`(i₀)_* (𝒪_{W₀} ^ ι) ⟶ Iₙ` is an isomorphism.

The noetherian hypothesis on the stalk makes `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` finitely
generated, which is what bounds the rank. -/
theorem exists_isIso_pushforwardFreeToThickeningIdeal [Flat f]
    [IsNoetherianRing (T.presheaf.stalk t)] :
    ∃ (ι : Type u) (_ : Fintype ι) (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤)),
      IsIso (pushforwardFreeToThickeningIdeal f t n m) := by
  obtain ⟨ι, hι, e, m, hspan, hind, hm⟩ :=
    exists_span_eq_and_forall_toModulesι_app_eq f t n
  exact ⟨ι, hι, m, isIso_pushforwardFreeToThickeningIdeal f t n m hspan hind hm⟩

/-- **The thickening ideal of a flat infinitesimal thickening, as a sheaf of modules, is the
pushforward of a free module of finite rank on the zeroth infinitesimal neighbourhood.** This
is the bare isomorphism statement; the isomorphism produced is the comparison morphism of
`AlgebraicGeometry.Scheme.exists_isIso_pushforwardFreeToThickeningIdeal`, which is the form to
use when the sections `m` matter. -/
theorem exists_nonempty_iso_thickeningIdeal_toModules [Flat f]
    [IsNoetherianRing (T.presheaf.stalk t)] :
    ∃ (ι : Type u) (_ : Fintype ι),
      Nonempty ((Modules.pushforward (infinitesimalBaseChangeMapZero f t n)).obj
        ((infinitesimalBaseChange f t 0).freeModules ι) ≅ (thickeningIdeal f t n).toModules) := by
  obtain ⟨ι, hι, m, hm⟩ := exists_isIso_pushforwardFreeToThickeningIdeal f t n
  exact ⟨ι, hι, ⟨asIso (pushforwardFreeToThickeningIdeal f t n m)⟩⟩

end AlgebraicGeometry.Scheme
