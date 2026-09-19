/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Seesaw
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.Tower
public import WeilConjectures.AlgebraicGeometry.TrivialityLocus
public import WeilConjectures.AlgebraicGeometry.TrivialityNearPoint

/-!
# The theorem of the cube

Let `X` and `Y` be proper geometrically integral varieties over a field `K`, let `Z` be a
connected reduced `K`-scheme of finite type, and let `x₀`, `y₀`, `z₀` be rational points of
`X`, `Y` and `Z`. If a line bundle `L` on `X × Y × Z` is trivial on each of the three slices

```
   X × {y₀} × Z ───▶   (X ×_K Y) ×_K Z   ◀─── {x₀} × Y × Z
                              ▲
                              │
                        X × Y × {z₀}
```

then `L` is trivial. This is `thm:cube-cube` of the blueprint
(`27_theorem_of_the_cube.tex`), and it is what this file proves.

Writing `W := X ×_K Y` — a proper variety, by
`AlgebraicGeometry.IsVariety.comp_fst` — and reading `X × Y × Z` as `W × Z`, the argument is
about the triviality locus

`Z' := {t : Z | L restricted to the fibre W_t is trivial}`

inside the base `Z` of the projection `p := pullback.snd (pullback.fst πX πY ≫ πX) πZ`:

```
   X × {y₀} × Z ───▶   (X ×_K Y) ×_K Z   ◀─── {x₀} × Y × Z
                              │
                              │ p
                              ▼
                              Z
```

* `Z'` is **closed**, by `cor:cube-triviality-closed`, which is
  `isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules` in the namespace
  `AlgebraicGeometry.Scheme.Modules`.
* `Z'` is **open**: at a point `t` of `Z'`, `lem:cube-thickening-trivial`
  (`AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper`) makes `L`
  trivial on every infinitesimal neighbourhood `W ×_Z Zₙ` of the fibre, and
  `prop:cube-formal-triviality`
  (`exists_mem_forall_nonempty_restrictToFiber_pullbackSnd_iso_structureModules`, in the same
  namespace) turns that into triviality on the fibres over a whole neighbourhood of `t`.
* `Z'` is non-empty, containing the point picked out by `z₀`.
* Hence `Z' = Z`, `Z` being connected, and `cor:cube-seesaw-trivial`
  (`AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_pullbackSnd`) applied to the
  rational point `(x₀, y₀)` of `W` concludes.

## Main statements

All three are in the namespace `AlgebraicGeometry.Scheme.Modules`.

- `isOpen_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules_of_sliceInclusion` —
  the triviality locus of `L` on `Z` is open. This is Steps 2 and 3 of the blueprint's proof.
- `nonempty_iso_structureModules_of_nonempty_restrictToFiber_pullbackSnd` — the theorem of the
  cube, asking triviality of `L` on the fibre over an arbitrary point of `Z`.
- `nonempty_iso_structureModules_of_map_sliceInclusion_eq_one` (blueprint: `thm:cube-cube`) —
  the theorem of the cube in the form the blueprint states it, asking triviality of `L` on the
  slice `X × Y × {z₀}` through a rational point `z₀`.

## Implementation notes

* **The Künneth hypothesis is carried, not discharged.** All three statements take the
  hypothesis `AlgebraicGeometry.Scheme.IsCubeKunneth` — that a deformation class on
  `(W ×_K Z) ×_Z Z_{n+1}` restricting to zero on both slices is zero — and pass it straight
  on, exactly as `WeilConjectures.AlgebraicGeometry.TheoremOfCube.Tower` carries it; see the
  implementation notes of that file for what it is and where it comes from in the blueprint.
  It is quantified here over the base point `t` of the tower as well as over `n`, because the
  proof runs the infinitesimal tower not only at `z₀` but at every point of the triviality
  locus. Discharging it is the work of a separate issue, after which the unconditional form of
  `thm:cube-cube` follows by supplying the resulting theorem.
* **Rationality of `z₀` is not used, and neither is the Jacobson argument of Step 3 of the
  blueprint.** The blueprint runs the infinitesimal tower at the `k`-rational points of `Z'`
  only, so it has to know that those are dense among the closed points and then invoke the
  Jacobson property of a finite-type `k`-scheme to see that the resulting open set exhausts
  `Z'`. The Lean form of `lem:cube-thickening-trivial` used here,
  `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper`, holds at an
  *arbitrary* point `t` of `Z` — rationality of the base point of the tower is what converts
  the slice `X × Y × {z₀}` into the base case of the induction, and here the base case is taken
  on the fibre instead — and so does `prop:cube-formal-triviality`. Openness of `Z'` therefore
  follows directly, algebraic closedness of the field is not needed anywhere, and the theorem
  is proved first in the form that asks only for *some* point of `Z'`.
* The two spellings of triviality are bridged by
  `AlgebraicGeometry.Scheme.Pic.map_mk_eq_one_iff`, in
  `WeilConjectures.AlgebraicGeometry.Modules.TrivialityCriterion`, and by
  `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_zero_mk_eq_one_iff`, in
  `WeilConjectures.AlgebraicGeometry.TrivialityNearPoint`.
* Everything here is `sorryAx`-tainted, through the seesaw theorem and through
  `prop:cube-formal-triviality`, both of which rest on the project's deferred semicontinuity
  and Grauert statements. This is why nothing in this area carries `\leanok`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-! ### The theorem of the cube -/

section Cube

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}}
  (πX : X ⟶ Spec (.of K)) [IsProper πX] [GeometricallyIntegral πX]
  (πY : Y ⟶ Spec (.of K)) [IsProper πY] [GeometricallyIntegral πY]
  (πZ : Z ⟶ Spec (.of K)) [LocallyOfFiniteType πZ]
  (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _)
  (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _)
  (hkunneth : ∀ (t : Z) (n : ℕ), IsCubeKunneth πX πY πZ x₀ hx₀ y₀ hy₀ t n)

include hkunneth

/-- **The triviality locus of `L` on `Z` is open** (blueprint: Steps 2 and 3 of the proof of
`thm:cube-cube`).

Let `X` and `Y` be proper geometrically integral varieties over a field `K`, let `Z` be a
`K`-scheme locally of finite type and let `L` be a line bundle on `(X ×_K Y) ×_K Z` whose
restrictions to the two slices of the triple product are trivial:

```
   X × {y₀} × Z ───▶   (X ×_K Y) ×_K Z   ◀─── {x₀} × Y × Z
                              │
                              │ pullback.snd (pullback.fst πX πY ≫ πX) πZ
                              ▼
                              Z
```

Then the set of points `t` of `Z` at which the restriction of `L` to the fibre `(X × Y)_t` is
trivial is open.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem isOpen_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules_of_sliceInclusion
    {L : (Limits.pullback (Limits.pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (hLX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1) :
    IsOpen {t : Z | Nonempty ((restrictToFiber
        (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ) t).obj L ≅
      ((Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ).fiber t).structureModules)} := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian πZ
  rw [isOpen_iff_mem_nhds]
  intro t ht
  -- `lem:cube-thickening-trivial` at `t` makes `L` trivial on every infinitesimal
  -- neighbourhood of the fibre over `t`
  have hF (n : ℕ) : Nonempty ((pullback (infinitesimalBaseChangeFst
      (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ) t n)).obj L ≅
        (infinitesimalBaseChange
          (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ) t n).structureModules) := by
    rw [← Pic.map_mk_eq_one_iff _ hL]
    exact Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper πX πY πZ x₀ hx₀ y₀ hy₀ t
      (hkunneth t) hL hLX hLY
      ((Pic.map_infinitesimalBaseChangeFst_zero_mk_eq_one_iff _ t hL).2 ht) n
  -- `prop:cube-formal-triviality` turns that into triviality on the fibres over a whole
  -- neighbourhood of `t`
  obtain ⟨V, htV, hV⟩ :=
    exists_mem_forall_nonempty_restrictToFiber_pullbackSnd_iso_structureModules
      (Limits.pullback.fst πX πY ≫ πX) πZ t hL hF
  exact mem_nhds_iff.2 ⟨V, hV, V.isOpen, htV⟩

variable [IsReduced Z] [ConnectedSpace Z] [QuasiCompact πZ]

/-- **The theorem of the cube, at an arbitrary point of `Z`.**

Let `X` and `Y` be proper geometrically integral varieties over a field `K`, let `Z` be a
connected reduced `K`-scheme of finite type, and let `x₀` and `y₀` be rational points of `X`
and `Y`. Let `L` be a line bundle on `(X ×_K Y) ×_K Z` whose restrictions to the two slices
`X × {y₀} × Z` and `{x₀} × Y × Z` are trivial and which is trivial on the fibre over *some*
point `t₀` of `Z`. Then `L` is trivial.

The point `t₀` is not asked to be rational: only `x₀` and `y₀` are, and they are rational
because the seesaw theorem is applied at the rational point `(x₀, y₀)` of `X ×_K Y`. The
blueprint form of the theorem, which asks triviality on the slice `X × Y × {z₀}` through a
rational point `z₀` of `Z`, is
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_of_map_sliceInclusion_eq_one`
below.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem nonempty_iso_structureModules_of_nonempty_restrictToFiber_pullbackSnd
    {L : (Limits.pullback (Limits.pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (t₀ : Z) (ht₀ : Nonempty ((restrictToFiber
      (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ) t₀).obj L ≅
        ((Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ).fiber t₀).structureModules))
    (hLX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1) :
    Nonempty (L ≅ (Limits.pullback (Limits.pullback.fst πX πY ≫ πX) πZ).structureModules) := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType πZ
  -- Step 1: the triviality locus is closed
  have hclosed : IsClosed {t : Z | Nonempty ((restrictToFiber
      (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ) t).obj L ≅
        ((Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ).fiber t).structureModules)} :=
    isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules _ πZ hL
  -- Steps 2 and 3: the triviality locus is open
  have hopen :=
    isOpen_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules_of_sliceInclusion
      πX πY πZ x₀ hx₀ y₀ hy₀ hkunneth hL hLX hLY
  -- Step 4: `Z` being connected, the triviality locus is all of `Z`
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, ht₀⟩
  -- Step 5: the seesaw theorem at the rational point `(x₀, y₀)` of `X ×_K Y`
  have hxy : x₀ ≫ πX = y₀ ≫ πY := by rw [hx₀, hy₀]
  have hw₀ : Limits.pullback.lift x₀ y₀ hxy ≫ (Limits.pullback.fst πX πY ≫ πX) = 𝟙 _ := by
    rw [← Category.assoc, Limits.pullback.lift_fst, hx₀]
  have hy : y₀ ≫ sliceInclusionSnd πX πY x₀ hx₀ = Limits.pullback.lift x₀ y₀ hxy := by
    ext <;> simp [reassoc_of% hy₀]
  -- the slice of `Y × Z` through `y₀` factors the slice of `(X ×_K Y) × Z` through the
  -- rational point `w₀ = (x₀, y₀)` of `X ×_K Y`:
  --
  --                    {x₀} × Y × Z
  --                  ↗              ↘
  --        Z ───────────────────────────▶ (X ×_K Y) ×_K Z
  --                 slice through w₀
  have hcomp : sliceInclusionSnd πY πZ y₀ hy₀ ≫ pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀ =
      sliceInclusionSnd (Limits.pullback.fst πX πY ≫ πX) πZ _ hw₀ := by
    ext <;> simp [← hy]
  refine nonempty_iso_structureModules_pullbackSnd _ πZ hL
    (fun t _ ↦ huniv.ge (Set.mem_univ t)) _ hw₀ ((Pic.map_mk_eq_one_iff _ hL).1 ?_)
  rw [← hcomp, Pic.map_comp_apply, hLY, map_one]

/-- **The theorem of the cube** (blueprint: `thm:cube-cube`).

Let `X` and `Y` be proper geometrically integral varieties over a field `K`, let `Z` be a
connected reduced `K`-scheme of finite type, and let `x₀`, `y₀` and `z₀` be rational points of
`X`, `Y` and `Z`. Let `L` be a line bundle on `X × Y × Z` whose restrictions to the three
slices are trivial:

```
   X × {y₀} × Z ───▶   (X ×_K Y) ×_K Z   ◀─── {x₀} × Y × Z
                              ▲
                              │
                        X × Y × {z₀}
```

Then `L` is trivial.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem nonempty_iso_structureModules_of_map_sliceInclusion_eq_one
    (z₀ : Spec (.of K) ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 _)
    {L : (Limits.pullback (Limits.pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (hLz : Pic.map (sliceInclusionFst (Limits.pullback.fst πX πY ≫ πX) πZ z₀ hz₀)
      (Pic.mk L hL) = 1)
    (hLX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1) :
    Nonempty (L ≅ (Limits.pullback (Limits.pullback.fst πX πY ≫ πX) πZ).structureModules) :=
  nonempty_iso_structureModules_of_nonempty_restrictToFiber_pullbackSnd πX πY πZ x₀ hx₀ y₀ hy₀
    hkunneth hL (z₀ (IsLocalRing.closedPoint K))
    ((Pic.map_infinitesimalBaseChangeFst_zero_mk_eq_one_iff _ _ hL).1
      (Pic.map_infinitesimalBaseChangeFst_zero_eq_one_of_sliceInclusionFst _ πZ z₀ hz₀ _
        (fromInfinitesimalNeighborhood_zero_comp_of_comp_eq_id Z K πZ z₀ hz₀) hL hLz))
    hLX hLY

end Cube

end AlgebraicGeometry.Scheme.Modules
