/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ThickeningFree
public import WeilConjectures.Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# The ideal of a flat infinitesimal thickening is free over the zeroth neighbourhood

Let `f : W ⟶ T` be a **flat** morphism of schemes, let `t` be a point of `T`, write
`Wₘ := W ×_T Tₘ` for the base change of `f` along the `m`-th infinitesimal neighbourhood of
`t`, let `Iₙ` be the thickening ideal of `Wₙ ↪ W_{n+1}` and let `i₀ : W₀ ↪ W_{n+1}` be the
closed immersion of the zeroth infinitesimal neighbourhood.

This file proves what `WeilConjectures.AlgebraicGeometry.ThickeningFree` leaves open: the
comparison morphism of `AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal`, whose
`j`-th leg is multiplication by a global section `m j` of `Iₙ`, **is an isomorphism** when the
family `m : ι → Γ(Iₙ, ⊤)` lies over a `κ(t)`-basis of `𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2)`:

```
  (i₀)_* 𝒪_{W₀} ──(i₀)_* (ιFree j)──▶ (i₀)_* (𝒪_{W₀} ^ ι)
              ╲                                │
       · m j   ╲                               │ ≅  (when `f` is flat)
                ╲                              ▼
                 ╲───────────────────────────▶ Iₙ
```

So the thickening ideal of a flat infinitesimal thickening is, as a sheaf of modules, free on
the zeroth infinitesimal neighbourhood, of rank `dim_{κ(t)} (𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2))`.

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
  `S` over `B` (`AlgebraicGeometry.Scheme.flat_stalk_infinitesimalBaseChange`) transports
  that to `S` by the equational criterion, in the form
  `Module.Flat.mem_ideal_map_of_sum_mul_eq_zero`.

Flatness of `f` therefore enters exactly once, and only through the second hypothesis; in fact
only flatness of `f` at the points of `W` lying over `t` is used, but the project has no
local-flatness predicate, so the results are stated with the global `[Flat f]`.

## Main results

- `AlgebraicGeometry.Scheme.isIso_pushforwardFreeToThickeningIdeal` — the comparison morphism
  attached to a family of global sections lying over a residue-field basis of `K` is an
  isomorphism.
- `AlgebraicGeometry.Scheme.exists_isIso_pushforwardFreeToThickeningIdeal_of_span` — the same,
  with the sections produced from a given basis `e` of `K`. The index type and the family `e`
  are data of `(T, t, n)` alone, so this is the form to use when several morphisms `f` over
  the same base point have to be compared.
- `AlgebraicGeometry.Scheme.exists_isIso_pushforwardFreeToThickeningIdeal` — such an index type
  and such a family `m` exist as soon as `K` is finitely generated, the index type having
  cardinality `dim_{κ(t)} K`, and
  `AlgebraicGeometry.Scheme.exists_isIso_pushforwardFreeToThickeningIdeal_of_isNoetherian` —
  the same for a noetherian stalk `𝒪_{T, t}`. These are the forms to feed to
  `WeilConjectures.AlgebraicGeometry.Cohomology.ThickeningFree`, whose results take the
  `IsIso` as an instance hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {T W : Scheme.{u}} (f : W ⟶ T) (t : T) (n : ℕ)

/-- **The comparison morphism `(i₀)_* (𝒪_{W₀} ^ ι) ⟶ Iₙ` is an isomorphism** when the global
sections `m j` of the thickening ideal lie over a family `e : ι → B` spanning
`K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` all of whose relations have coefficients in `𝔪_B`,
that is, over a `κ(t)`-basis of `K`, and when `f` is flat.

```
  (i₀)_* 𝒪_{W₀} ──(i₀)_* (ιFree j)──▶ (i₀)_* (𝒪_{W₀} ^ ι)
              ╲                                │
       · m j   ╲                               │ ≅  (when `f` is flat)
                ╲                              ▼
                 ╲───────────────────────────▶ Iₙ
```

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
  have hgerm (x : infinitesimalBaseChange f t (n + 1)) (j : ι) :
      (infinitesimalBaseChange f t (n + 1)).presheaf.germ ⊤ x trivial
          ((thickeningIdeal f t n).toModulesι.app ⊤ (m j)) =
        infinitesimalRingToStalk f t (n + 1) x (e j) := by
    rw [hm j, germ_infinitesimalRingToΓ]
  refine IdealSheafData.isIso_pushforwardFreeDesc (infinitesimalBaseChangeMapZero f t n)
    (ker_mul_thickeningIdeal_eq_zero f t n) m (fun x c hc j ↦ ?_) fun x ↦ ?_
  · -- the relations between the `m j` on the stalk have coefficients in `𝔪_B S`
    let _ : Algebra (T.infinitesimalRing t (n + 1))
        ((infinitesimalBaseChange f t (n + 1)).presheaf.stalk x) :=
      (infinitesimalRingToStalk f t (n + 1) x).hom.toAlgebra
    have _ := flat_stalk_infinitesimalBaseChange f t (n + 1) x
    rw [stalkIdeal_ker_infinitesimalBaseChangeMapZero]
    exact Module.Flat.mem_ideal_map_of_sum_mul_eq_zero hind
      (by simpa only [hgerm x, RingHom.algebraMap_toAlgebra] using hc) j
  · -- the stalk of `Iₙ` is the extension of `K`, which the `e j` span
    rw [stalkIdeal_thickeningIdeal, ← hspan, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨j, hgerm x j⟩

/-- **A `κ(t)`-basis `e` of `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` is realized by a family of
global sections of the thickening ideal for which the comparison morphism
`(i₀)_* (𝒪_{W₀} ^ ι) ⟶ Iₙ` is an isomorphism**, when `f` is flat.

The index type `ι` and the family `e` depend only on `T`, `t` and `n`, not on `f`, so this is
the form to use when the identification is needed simultaneously for several morphisms to `T`:
the sections `m` for each of them then lie over the *same* family `e`. -/
theorem exists_isIso_pushforwardFreeToThickeningIdeal_of_span [Flat f] {ι : Type u} [Fintype ι]
    (e : ι → T.infinitesimalRing t (n + 1))
    (hspan : Ideal.span (Set.range e) =
      RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom)
    (hind : ∀ c : ι → T.infinitesimalRing t (n + 1), ∑ i, c i * e i = 0 →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal (T.infinitesimalRing t (n + 1))) :
    ∃ m : ι → Γ((thickeningIdeal f t n).toModules, ⊤),
      (∀ j, (thickeningIdeal f t n).toModulesι.app ⊤ (m j) =
        infinitesimalRingToΓ f t (n + 1) (e j)) ∧
      IsIso (pushforwardFreeToThickeningIdeal f t n m) := by
  obtain ⟨m, hm⟩ := exists_forall_toModulesι_app_eq_infinitesimalRingToΓ f t n e
    fun j ↦ hspan ▸ Ideal.subset_span ⟨j, rfl⟩
  exact ⟨m, hm, isIso_pushforwardFreeToThickeningIdeal f t n m hspan hind hm⟩

/-- **The thickening ideal of a flat infinitesimal thickening is free on the zeroth
infinitesimal neighbourhood, of rank `dim_{κ(t)} K`**: there is a finite index type `ι` of
cardinality `dim_{κ(t)} K` and a family `m` of global sections of `Iₙ` for which the comparison
morphism `(i₀)_* (𝒪_{W₀} ^ ι) ⟶ Iₙ` is an isomorphism.

The hypothesis is that `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` is finitely generated; see
`AlgebraicGeometry.Scheme.exists_isIso_pushforwardFreeToThickeningIdeal_of_isNoetherian` for
the form that derives it from a noetherian stalk. -/
theorem exists_isIso_pushforwardFreeToThickeningIdeal [Flat f]
    (hfg : (RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom).FG) :
    ∃ (ι : Type u) (_ : Finite ι) (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤)),
      IsIso (pushforwardFreeToThickeningIdeal f t n m) ∧
      Nat.card ι = Module.finrank (T.infinitesimalRing t (n + 1) ⧸
          IsLocalRing.maximalIdeal (T.infinitesimalRing t (n + 1)))
        (RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom) := by
  obtain ⟨ι, hι, e, m, hspan, hind, hm, hrank⟩ :=
    exists_span_eq_and_forall_toModulesι_app_eq f t n hfg
  exact ⟨ι, inferInstance, m,
    isIso_pushforwardFreeToThickeningIdeal f t n m hspan hind hm, hrank⟩

/-- **The thickening ideal of a flat infinitesimal thickening over a noetherian local ring is
free on the zeroth infinitesimal neighbourhood, of rank `dim_{κ(t)} K`.** This is
`AlgebraicGeometry.Scheme.exists_isIso_pushforwardFreeToThickeningIdeal` with the finite
generation of `K` supplied by `AlgebraicGeometry.Scheme.fg_ker_infinitesimalRingMap`; it is the
form to use over a noetherian base. -/
theorem exists_isIso_pushforwardFreeToThickeningIdeal_of_isNoetherian [Flat f]
    [IsNoetherianRing (T.presheaf.stalk t)] :
    ∃ (ι : Type u) (_ : Finite ι) (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤)),
      IsIso (pushforwardFreeToThickeningIdeal f t n m) ∧
      Nat.card ι = Module.finrank (T.infinitesimalRing t (n + 1) ⧸
          IsLocalRing.maximalIdeal (T.infinitesimalRing t (n + 1)))
        (RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom) :=
  exists_isIso_pushforwardFreeToThickeningIdeal f t n
    (T.fg_ker_infinitesimalRingMap t (Nat.le_succ n))

end AlgebraicGeometry.Scheme
