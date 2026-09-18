/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Seesaw
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube
public import WeilConjectures.AlgebraicGeometry.TrivialityLocus
public import WeilConjectures.AlgebraicGeometry.TrivialityNearPoint

/-!
# The theorem of the cube

Let `X` and `Y` be proper geometrically integral varieties over a field `K`, let `Z` be a
connected reduced `K`-scheme of finite type, and let `x₀`, `y₀`, `z₀` be rational points of
`X`, `Y` and `Z`. If a line bundle `L` on `X × Y × Z` is trivial on each of the three slices

`{x₀} × Y × Z`,   `X × {y₀} × Z`,   `X × Y × {z₀}`

then `L` is trivial. This is `thm:cube-cube` of the blueprint
(`27_theorem_of_the_cube.tex`), and it is what this file proves.

Writing `W := X ×_K Y` — a proper variety, by
`AlgebraicGeometry.IsVariety.comp_fst` — and reading `X × Y × Z` as `W × Z`, the argument is
about the triviality locus

`Z' := {t : Z | L restricted to the fibre W_t is trivial}`.

* `Z'` is **closed**, by `cor:cube-triviality-closed`
  (`AlgebraicGeometry.Scheme.Modules.isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules`).
* `Z'` is **open**: at a point `t` of `Z'`, `lem:cube-thickening-trivial`
  (`AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper`) makes `L`
  trivial on every infinitesimal neighbourhood `W ×_Z Zₙ` of the fibre, and
  `prop:cube-formal-triviality`
  (`AlgebraicGeometry.Scheme.Modules.exists_mem_forall_nonempty_restrictToFiber_pullbackSnd_iso_structureModules`)
  turns that into triviality on the fibres over a whole neighbourhood of `t`.
* `Z'` contains the point picked out by `z₀`, by the third hypothesis.
* Hence `Z' = Z`, `Z` being connected, and `cor:cube-seesaw-trivial`
  (`AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_pullbackSnd`) applied to the
  rational point `(x₀, y₀)` of `W` concludes.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isOpen_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules`
  — the triviality locus of `L` on `Z` is open. This is Steps 2 and 3 of the blueprint's proof.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_of_pullbackMapSliceInclusion`
  (blueprint: `thm:cube-cube`) — the theorem of the cube itself.

## Implementation notes

* **The Künneth hypothesis is carried, not discharged.** Both statements take the hypothesis
  `hkunneth` of
  `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_pullbackMapSliceInclusion_eq_one_of_isProper`
  — that a deformation class on `(W ×_K Z) ×_Z Z_{n+1}` restricting to zero on both slices is
  zero — and pass it straight on, exactly as `WeilConjectures.AlgebraicGeometry.TheoremOfCube`
  carries it; see the implementation notes of that file for what it is and where it comes from
  in the blueprint. It is quantified here over the base point `t` of the tower as well as over
  `n`, because the proof runs the infinitesimal tower not only at `z₀` but at every point of
  the triviality locus. Discharging it is the work of a separate issue, after which the
  unconditional form of `thm:cube-cube` follows by supplying the resulting theorem.
* **The Jacobson argument of Step 3 of the blueprint is not needed here.** The blueprint runs
  the infinitesimal tower at the `k`-rational points of `Z'` only, so it has to know that those
  are dense among the closed points and then invoke the Jacobson property of a finite-type
  `k`-scheme to see that the resulting open set exhausts `Z'`. The Lean form of
  `lem:cube-thickening-trivial` used here,
  `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper`, holds at an
  *arbitrary* point `t` of `Z` — rationality of the base point of the tower is what converts
  the slice `X × Y × {z₀}` into the base case of the induction, and here the base case is taken
  on the fibre instead — and so does `prop:cube-formal-triviality`. Openness of `Z'` therefore
  follows directly, and algebraic closedness of the field is not needed anywhere.
* The two spellings of triviality are bridged by
  `AlgebraicGeometry.Scheme.Pic.map_eq_one_iff`, which says that the class of the pullback of
  `L` along `f` is trivial in the Picard group exactly when `f^* L ≅ 𝒪`, and by
  `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_zero_eq_one_iff`, which
  identifies the zeroth infinitesimal base change `W ×_Z Z₀` with the fibre `W_t`.
* Everything here is `sorryAx`-tainted, through the seesaw theorem and through
  `prop:cube-formal-triviality`, both of which rest on the project's deferred semicontinuity
  and Grauert statements. This is why nothing in this area carries `\leanok`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-! ### Triviality of a pullback in the Picard group -/

section Pic

variable {X Y : Scheme.{u}}

/-- **Pullback along an isomorphism is injective on Picard groups**, its inverse being pullback
along the inverse isomorphism. -/
theorem Pic.map_injective_of_isIso (f : X ⟶ Y) [IsIso f] : Function.Injective (Pic.map f) :=
  Function.LeftInverse.injective (g := Pic.map (inv f)) fun x ↦ by
    rw [← Pic.map_comp_apply, IsIso.inv_hom_id, Pic.map_id, MonoidHom.id_apply]

/-- **The class of a pullback is trivial in the Picard group exactly when the pullback is
isomorphic to the structure sheaf.** This is the bridge between the two spellings of
"`L` is trivial": the `Pic`-theoretic one of
`WeilConjectures.AlgebraicGeometry.TheoremOfCube` and the sheaf-theoretic one of
`WeilConjectures.AlgebraicGeometry.Seesaw`. -/
theorem Pic.map_eq_one_iff (f : X ⟶ Y) {L : Y.Modules} (hL : L.Invertible) :
    Pic.map f (Pic.mk L hL) = 1 ↔
      Nonempty ((Modules.pullback f).obj L ≅ X.structureModules) := by
  rw [Pic.map_mk, Pic.mk_eq_one_iff, Modules.nonempty_iso_structureModules_iff]

end Pic

section Fiber

variable {W T : Scheme.{u}}

/-- **Triviality on the zeroth infinitesimal base change is triviality on the fibre**: the
identification `W ×_T T₀ ≅ W_t` of `AlgebraicGeometry.Scheme.infinitesimalBaseChangeZeroIsoFiber`
carries one to the other. -/
theorem Pic.map_infinitesimalBaseChangeFst_zero_eq_one_iff (f : W ⟶ T) (t : T) {L : W.Modules}
    (hL : L.Invertible) :
    Pic.map (infinitesimalBaseChangeFst f t 0) (Pic.mk L hL) = 1 ↔
      Nonempty ((Modules.restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) := by
  rw [← Pic.map_eq_one_iff, ← infinitesimalBaseChangeZeroIsoFiber_hom_fiberι f t,
    Pic.map_comp_apply]
  refine ⟨fun h ↦ Pic.map_injective_of_isIso _ (h.trans (map_one _).symm), fun h ↦ ?_⟩
  rw [h, map_one]

end Fiber

namespace Modules

/-! ### The theorem of the cube -/

section Cube

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}}
  (πX : X ⟶ Spec (.of K)) [IsProper πX] [GeometricallyIntegral πX]
  (πY : Y ⟶ Spec (.of K)) [IsProper πY] [GeometricallyIntegral πY]
  (πZ : Z ⟶ Spec (.of K)) [LocallyOfFiniteType πZ] [QuasiCompact πZ]
  (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _)
  (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _)

/-- **The triviality locus of `L` on `Z` is open** (blueprint: Steps 2 and 3 of the proof of
`thm:cube-cube`).

Let `X` and `Y` be proper geometrically integral varieties over a field `K`, let `Z` be a
`K`-scheme of finite type and let `L` be a line bundle on `(X ×_K Y) ×_K Z` whose restrictions
to `X × {y₀} × Z` and `{x₀} × Y × Z` are trivial. Then the set of points `t` of `Z` at which
the restriction of `L` to the fibre `(X × Y)_t` is trivial is open.

At such a `t`, `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper`
makes `L` trivial on every infinitesimal neighbourhood of the fibre, and
`AlgebraicGeometry.Scheme.Modules.exists_mem_forall_nonempty_restrictToFiber_pullbackSnd_iso_structureModules`
turns that into triviality on the fibres over a neighbourhood of `t`.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem isOpen_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules
    (hkunneth : ∀ (t : Z) (n : ℕ), Function.Injective
      ((thickeningH1Map (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ)
            (Limits.pullback.snd πX πZ) (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀)
            (pullbackMapSliceInclusionFst_snd πX πY πZ y₀ hy₀) t n).prod
        (thickeningH1Map (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ)
            (Limits.pullback.snd πY πZ) (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀)
            (pullbackMapSliceInclusionSnd_snd πX πY πZ x₀ hx₀) t n)))
    {L : (Limits.pullback (Limits.pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (hLX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1) :
    IsOpen {t : Z | Nonempty ((restrictToFiber
        (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ) t).obj L ≅
      ((Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ).fiber t).structureModules)} := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType πZ
  have : IsVariety (Limits.pullback.fst πX πY ≫ πX) := inferInstance
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have hF : ∀ n : ℕ, Nonempty ((pullback (infinitesimalBaseChangeFst
      (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ) t n)).obj L ≅
        (infinitesimalBaseChange
          (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ) t n).structureModules) := by
    intro n
    rw [← Pic.map_eq_one_iff]
    exact Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper πX πY πZ x₀ hx₀ y₀ hy₀ t
      (hkunneth t) hL hLX hLY
      ((Pic.map_infinitesimalBaseChangeFst_zero_eq_one_iff _ t hL).2 ht) n
  obtain ⟨V, htV, hV⟩ :=
    exists_mem_forall_nonempty_restrictToFiber_pullbackSnd_iso_structureModules
      (Limits.pullback.fst πX πY ≫ πX) πZ t hL hF
  exact mem_nhds_iff.2 ⟨V, hV, V.2, htV⟩

/-- **The theorem of the cube** (blueprint: `thm:cube-cube`).

Let `X` and `Y` be proper geometrically integral varieties over a field `K`, let `Z` be a
connected reduced `K`-scheme of finite type, and let `x₀`, `y₀` and `z₀` be rational points of
`X`, `Y` and `Z`. Let `L` be a line bundle on `X × Y × Z` whose restrictions to the three
slices `X × {y₀} × Z`, `{x₀} × Y × Z` and `X × Y × {z₀}` are trivial. Then `L` is trivial.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem nonempty_iso_structureModules_of_pullbackMapSliceInclusion [IsReduced Z]
    [ConnectedSpace Z] (z₀ : Spec (.of K) ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 _)
    (hkunneth : ∀ (t : Z) (n : ℕ), Function.Injective
      ((thickeningH1Map (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ)
            (Limits.pullback.snd πX πZ) (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀)
            (pullbackMapSliceInclusionFst_snd πX πY πZ y₀ hy₀) t n).prod
        (thickeningH1Map (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ)
            (Limits.pullback.snd πY πZ) (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀)
            (pullbackMapSliceInclusionSnd_snd πX πY πZ x₀ hx₀) t n)))
    {L : (Limits.pullback (Limits.pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (hLz : Pic.map (sliceInclusionFst (Limits.pullback.fst πX πY ≫ πX) πZ z₀ hz₀)
      (Pic.mk L hL) = 1)
    (hLX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1) :
    Nonempty (L ≅ (Limits.pullback (Limits.pullback.fst πX πY ≫ πX) πZ).structureModules) := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType πZ
  have : IsVariety (Limits.pullback.fst πX πY ≫ πX) := inferInstance
  -- Step 1: the triviality locus is closed, and contains the point picked out by `z₀`
  have hclosed : IsClosed {t : Z | Nonempty ((restrictToFiber
      (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ) t).obj L ≅
        ((Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ).fiber t).structureModules)} :=
    isClosed_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules _ πZ hL
  have hz : Nonempty ((restrictToFiber
      (Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ)
        (z₀ (IsLocalRing.closedPoint K))).obj L ≅
      ((Limits.pullback.snd (Limits.pullback.fst πX πY ≫ πX) πZ).fiber
        (z₀ (IsLocalRing.closedPoint K))).structureModules) := by
    rw [← Pic.map_infinitesimalBaseChangeFst_zero_eq_one_iff _ _ hL,
      ← infinitesimalBaseChangeFst_zero_comp_sliceInclusionFst _ πZ z₀ hz₀ _
        (fromInfinitesimalNeighborhood_zero_comp_of_comp_eq_id Z K πZ z₀ hz₀),
      Pic.map_comp_apply, hLz, map_one]
  -- Steps 2 and 3: the triviality locus is open
  have hopen := isOpen_setOf_nonempty_restrictToFiber_pullbackSnd_iso_structureModules
    πX πY πZ x₀ hx₀ y₀ hy₀ hkunneth hL hLX hLY
  -- Step 4: `Z` being connected, the triviality locus is all of `Z`
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨_, hz⟩
  -- Step 5: the seesaw theorem at the rational point `(x₀, y₀)` of `X ×_K Y`
  have hxy : x₀ ≫ πX = y₀ ≫ πY := by rw [hx₀, hy₀]
  set w₀ := Limits.pullback.lift x₀ y₀ hxy with hw₀def
  have hw₀ : w₀ ≫ (Limits.pullback.fst πX πY ≫ πX) = 𝟙 _ := by
    rw [hw₀def, ← Category.assoc, Limits.pullback.lift_fst, hx₀]
  have hy : y₀ ≫ sliceInclusionSnd πX πY x₀ hx₀ = w₀ := by
    refine Limits.pullback.hom_ext ?_ ?_ <;> simp [hw₀def, reassoc_of% hy₀]
  have hcomp : sliceInclusionSnd πY πZ y₀ hy₀ ≫ pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀ =
      sliceInclusionSnd (Limits.pullback.fst πX πY ≫ πX) πZ w₀ hw₀ := by
    refine Limits.pullback.hom_ext ?_ ?_ <;>
      simp [← Category.assoc, ← hy, Category.assoc]
  refine nonempty_iso_structureModules_pullbackSnd _ πZ hL
    (fun t _ ↦ huniv.ge (Set.mem_univ t)) w₀ hw₀ ((Pic.map_eq_one_iff _ hL).1 ?_)
  rw [← hcomp, Pic.map_comp_apply, hLY, map_one]

end Cube

end Modules

end AlgebraicGeometry.Scheme
