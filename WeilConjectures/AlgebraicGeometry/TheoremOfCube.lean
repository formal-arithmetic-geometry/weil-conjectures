/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The theorem of the cube

Let `X`, `Y` be proper and geometrically integral over a field `K`, let `Z` be connected, and
let `x`, `y`, `z` be `K`-points of `X`, `Y`, `Z`. An invertible module on `X ×_K Y ×_K Z` is
determined, up to isomorphism, by its restrictions to the three slices `{x} × Y × Z`,
`X × {y} × Z` and `X × Y × {z}` (Stacks, Tag 0BF4).

Products are taken in the cartesian monoidal category `Over (Spec K)`, so that
`((X ⊗ Y) ⊗ Z).left` is the fibre product `(X ×_K Y) ×_K Z`, and the slice inclusions are
written with `CartesianMonoidalCategory.lift`.

## Main statements

- `AlgebraicGeometry.nonempty_iso_of_nonempty_iso_overPullback_slices`: the theorem of the cube.

The proof follows Stacks: the locus of points of `Z` over which `M` and `N` are locally
isomorphic is open, closed (`AlgebraicGeometry.isClosed_setOf_exists_nonempty_iso_preimageSnd`)
and contains `z` (`AlgebraicGeometry.exists_mem_nonempty_iso_preimageSnd`), hence is all of the
connected scheme `Z`, and an isomorphism locally over `Z` globalises
(`AlgebraicGeometry.nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

variable {K : Type u} [Field K]

/-- The open subscheme `X ×_K Y ×_K U` of `X ×_K Y ×_K Z` lying over an open `U ⊆ Z`. -/
noncomputable abbrev preimageSnd (X Y Z : Over (Spec (.of K))) (U : Z.left.Opens) :
    ((X ⊗ Y) ⊗ Z).left.Opens :=
  (snd (X ⊗ Y) Z).left ⁻¹ᵁ U

/-- **Closedness of the locus of triviality** (Stacks, Tags 0BDP, 0BF0 and 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `M`, `N` be invertible modules on `X ×_K Y ×_K Z` which become isomorphic on the slices
`{x} × Y × Z` and `X × {y} × Z`. Then the set of points `t ∈ Z` having an open neighbourhood
`U` with `M ≅ N` on `X ×_K Y ×_K U` is closed.

By Tag 0BF3 (applied over `Z`, using the two slices) this set is the set of `t` such that `M` and
`N` are isomorphic on the fibre over `t`, and by Tags 0BDP and 0BF0 that set is the image of a
closed immersion `Z' → Z`. -/
theorem isClosed_setOf_exists_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N)) :
    IsClosed {t : Z.left | ∃ U : Z.left.Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N)} :=
  sorry

/-- **Openness of the locus of triviality at a rational point** (Stacks, Tag 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `z` be a `K`-point of `Z`. If two invertible modules `M`, `N` on `X ×_K Y ×_K Z` become
isomorphic on the slices `{x} × Y × Z`, `X × {y} × Z` and `X × Y × {z}`, then they are
isomorphic on `X ×_K Y ×_K U` for some open neighbourhood `U` of `z`.

Tag 0BF3 is applied over the base `Z` to `X ×_K Z` and `Y ×_K Z` with the sections given by `x`
and `y`; its proof is an infinitesimal lifting argument based on the injectivity of
`H¹(X × Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` (Künneth). -/
theorem exists_mem_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (z : 𝟙_ _ ⟶ Z) (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N))
    (hz : Nonempty (overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) M ≅
      overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) N)) :
    ∃ U : Z.left.Opens, z.left.base (IsLocalRing.closedPoint K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N) :=
  sorry

/-- **Invertible modules isomorphic locally over the base are isomorphic** (Stacks, Tag 0BDP and
the last step of the proof of Tag 0BF4).

Let `X`, `Y` be proper and geometrically integral over a field `K` and let `x` be a `K`-point of
`X`. If two invertible modules `M`, `N` on `X ×_K Y ×_K Z` are isomorphic on `X ×_K Y ×_K U` for
the members `U` of an open cover of `Z`, and are isomorphic on the slice `{x} × Y × Z`, then
`M ≅ N`.

Since the pushforward of `𝒪` along `X ×_K Y ×_K Z → Z` is `𝒪_Z`, the invertible module
`L = M ⊗ N⁻¹`, being locally on `Z` trivial, is the pullback of the invertible module
`𝒩 = p_* L` on `Z`; pulling back along the section `x × y × id_Z` shows `𝒩 ≅ 𝒪_Z`. -/
theorem nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X)
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hloc : ∀ t : Z.left, ∃ U : Z.left.Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N))
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N)) :
    Nonempty (M ≅ N) :=
  sorry

/-- **The theorem of the cube** (Stacks, Tag 0BF4, over `S = Spec K` with `K`-rational points).

Let `X`, `Y` be proper and geometrically integral over a field `K`, let `Z` be a connected
`K`-scheme and let `x`, `y`, `z` be `K`-points of `X`, `Y`, `Z`. If two invertible modules `M`,
`N` on `X ×_K Y ×_K Z` become isomorphic on each of the three slices `{x} × Y × Z`,
`X × {y} × Z` and `X × Y × {z}`, then `M ≅ N`.

Stacks states this for one invertible module `L` (if `L` is trivial on the three slices then
`L` is trivial); the form here follows by applying it to `L = M ⊗ N⁻¹`. Over a field the
flatness and finite presentation hypotheses of Tag 0BF4 are automatic. -/
theorem nonempty_iso_of_nonempty_iso_overPullback_slices (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] [ConnectedSpace Z.left] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (z : 𝟙_ _ ⟶ Z) (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N))
    (hz : Nonempty (overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) M ≅
      overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) N)) :
    Nonempty (M ≅ N) := by
  -- The set of points of `Z` over which `M` and `N` are locally isomorphic is open by
  -- definition, closed and contains `z`, hence is all of `Z`.
  set T : Set Z.left := {t | ∃ U : Z.left.Opens, t ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
      (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N)} with hT
  have hopen : IsOpen T := isOpen_iff_forall_mem_open.2 fun _ ⟨U, htU, e⟩ =>
    ⟨U, fun _ ht' => ⟨U, ht', e⟩, U.isOpen, htU⟩
  have hclosed : IsClosed T :=
    isClosed_setOf_exists_nonempty_iso_preimageSnd X Y Z x y M N hx hy
  have hmem : z.left.base (IsLocalRing.closedPoint K) ∈ T :=
    exists_mem_nonempty_iso_preimageSnd X Y Z x y z M N hx hy hz
  have huniv : T = Set.univ :=
    (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨_, hmem⟩)
  exact nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd X Y Z x M N
    (fun t => show t ∈ T from huniv ▸ Set.mem_univ t) hx

end AlgebraicGeometry
