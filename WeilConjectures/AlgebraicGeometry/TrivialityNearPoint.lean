/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FormalTriviality
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialityCriterion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Formal triviality is triviality near the point

Let `X` be a proper geometrically integral variety over a field `K`, let `T` be a locally
Noetherian `K`-scheme, let `t₀` be a point of `T` and let `L` be a line bundle on `X × T` whose
pullback to `X × Tₙ` is trivial for every `n`, where `Tₙ = Spec (𝒪_{T, t₀} ⧸ 𝔪 ^ (n + 1))`. This
file proves that `L` is then trivial on the fibre `X_t` for every `t` in some open neighbourhood
of `t₀`.

The input is `AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_pullbackSnd_ne_zero`:
formal triviality produces a section `s` of `L` over `p_T ⁻¹ᵁ V₁` whose restriction to the fibre
`X_{t₀}` is non-zero, and likewise a section `u` of a tensor inverse `N` of `L` over
`p_T ⁻¹ᵁ V₂`. What this file adds is the argument that runs on those two sections, Steps 4 and 5
of the blueprint proof.

## Main statements

- `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_zero_mk_eq_one_iff`: triviality
  of `L` on `W ×_T T₀` is triviality of `L` on the fibre `W_t`.

The next two are in the namespace `AlgebraicGeometry.Scheme.Modules`.

- `eventually_nonempty_restrictToFiber_iso_structureModules`: for an arbitrary universally closed
  morphism `f : W ⟶ T` with geometrically integral fibres and sections of `f _* L` and `f _* N`
  over an open `V ∋ t₀` which are non-zero on the fibre over `t₀`, the restriction of `L` to the
  fibre `W_t` is trivial for every `t` in a neighbourhood of `t₀`.
- `exists_mem_forall_nonempty_restrictToFiber_pullbackSnd_iso_structureModules`: **formal
  triviality is triviality near the point**, the statement of the blueprint.

## Implementation notes

* The product `s ⊗ u` and the triviality criterion on a fibre come from
  `WeilConjectures.AlgebraicGeometry.Modules.TrivialityCriterion`. The criterion is used in the
  form
  `AlgebraicGeometry.Scheme.Modules.nonempty_restrictToFiber_iso_structureModules_iff_nontrivial`
  rather than through the fibrewise dimension, so that neither coherence nor the semicontinuity
  of `h⁰` enters.
* The blueprint shrinks `V` to an affine open and identifies `Γ(X × V, 𝒪)` with `Γ(V, 𝒪_V)` by
  base change, then takes the non-vanishing locus of `s ⊗ u` downstairs. Neither the shrinking
  nor the base change is needed: the non-vanishing locus of `s ⊗ u` is an open subset of
  `p_T ⁻¹ᵁ V` containing the whole fibre over `t₀`, and the tube lemma for closed maps
  (`IsClosedMap.eventually_nhds_fiber`) turns that into a neighbourhood of `t₀` downstairs. Only
  closedness of `f` is used, so the general statement asks for `UniversallyClosed` and not
  properness.
* Only the last statement is `sorry`-tainted, and only through
  `AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_pullbackSnd_ne_zero`, which is
  applied once for `L` and once for its tensor inverse.

## Blueprint

`prop:cube-formal-triviality` of
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- **Triviality on the zeroth infinitesimal base change is triviality on the fibre**: the two
are carried into each other by the identification
`AlgebraicGeometry.Scheme.infinitesimalBaseChangeZeroIsoFiber` of `W ×_T T₀` with `W_t`, which
commutes with the two morphisms to `W`.

```
   W ×_T T₀ ──────────────≅─────────────▶ W_t
         ╲                                 │
           ╲                               │ f.fiberι t
             ╲  ibcFst f t 0               │
               ╲                           ▼
                 ──────────────────────▶   W
```

Here `ibcFst f t 0` is `AlgebraicGeometry.Scheme.infinitesimalBaseChangeFst f t 0`. -/
theorem Pic.map_infinitesimalBaseChangeFst_zero_mk_eq_one_iff {W T : Scheme.{u}} (f : W ⟶ T)
    (t : T) {L : W.Modules} (hL : L.Invertible) :
    Pic.map (infinitesimalBaseChangeFst f t 0) (Pic.mk L hL) = 1 ↔
      Nonempty ((Modules.restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) := by
  rw [← Pic.map_mk_eq_one_iff _ hL, ← infinitesimalBaseChangeZeroIsoFiber_hom_fiberι f t,
    Pic.map_comp_apply]
  exact _root_.map_eq_one_iff _ (Pic.map_injective_of_isIso _)

namespace Modules

noncomputable section

section NearPoint

variable {W T : Scheme.{u}}

/-- **A line bundle carrying sections which are non-zero on one fibre is trivial on every nearby
fibre.**

Let `f : W ⟶ T` be a universally closed morphism whose fibres over an open `V` are geometrically
integral, let `L` and `N` be sheaves of modules on `W` with `e : L ⊗ N ≅ 𝒪_W`, and let `t₀` be a
point of `V`. If `L` and `N` have sections over `f ⁻¹ᵁ V` whose restrictions to the fibre
`W_{t₀}` are non-zero, then `L` is trivial on the fibre `W_t` for every `t` in a neighbourhood of
`t₀`.

The non-vanishing locus of the product `s ⊗ u` is an open subset of `f ⁻¹ᵁ V` containing the
whole fibre over `t₀`, because `L` and `N` are trivial on that fibre and a non-zero section of a
trivial line bundle on an integral scheme, universally closed over a field, vanishes nowhere
(`AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_universallyClosed`). The tube lemma for
closed maps therefore makes it contain the whole fibre over every `t` near `t₀`, and at such a
`t` the non-vanishing of `s ⊗ u` on `W_t` forces both `s` and `u` to be non-zero there.

This is Steps 4 and 5 of the proof of `prop:cube-formal-triviality` of the blueprint. -/
theorem eventually_nonempty_restrictToFiber_iso_structureModules (f : W ⟶ T)
    [UniversallyClosed f] {L N : W.Modules} (e : L ⊗ N ≅ 𝟙_ W.Modules)
    {t₀ : T} {V : T.Opens} (hV : t₀ ∈ V)
    (hgeom : ∀ t ∈ V, GeometricallyIntegral (f.fiberToSpecResidueField t))
    (s : Γ((pushforward f).obj L, V)) (hs : fiberSectionsOfNhds f L t₀ V hV s ≠ 0)
    (u : Γ((pushforward f).obj N, V)) (hu : fiberSectionsOfNhds f N t₀ V hV u ≠ 0) :
    ∀ᶠ t in nhds t₀, Nonempty ((restrictToFiber f t).obj L ≅ (f.fiber t).structureModules) := by
  -- the geometric integrality of the fibre over `t₀` is an instance for the criterion below
  have := hgeom t₀ hV
  have : IsIntegral (f.fiber t₀) := GeometricallyIntegral.isIntegral (f.fiberToSpecResidueField t₀)
  -- both `L` and `N` are trivial on the fibre over `t₀`, because they have non-zero sections there
  have hLunit : (restrictToFiber f t₀).obj L ≅ (f.fiber t₀).structureModules :=
    ((nonempty_restrictToFiber_iso_structureModules_iff_nontrivial f e t₀).2
      ⟨nontrivial_of_ne _ 0 hs, nontrivial_of_ne _ 0 hu⟩).some
  have hNunit : (restrictToFiber f t₀).obj N ≅ (f.fiber t₀).structureModules :=
    isoStructureModulesOfTensorIso (Functor.Monoidal.mapIsoTensorUnit (restrictToFiber f t₀) e)
      hLunit
  -- the locus, inside `f ⁻¹ᵁ V`, on which the product of `s` and `u` does not vanish
  set Ω : Set W := (f ⁻¹ᵁ V).ι.base ''
    {y : (f ⁻¹ᵁ V).toScheme | fiberMap (pairingHomOfNhds f e s u) y ≠ 0}
  have hΩopen : IsOpen Ω :=
    (f ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap _
      (isClosed_setOf_fiberMap_eq_zero
        (SheafOfModules.invertible_tensorUnit (f ⁻¹ᵁ V).toScheme.sheaf)
        (SheafOfModules.invertible_tensorUnit (f ⁻¹ᵁ V).toScheme.sheaf)
        (pairingHomOfNhds f e s u)).isOpen_compl
  -- a point of the fibre over `t` lies in `Ω` exactly when the product does not vanish there
  have hmem : ∀ (t : T) (ht : t ∈ V) (x : f.fiber t),
      f.fiberι t x ∈ Ω ↔ fiberMap (pairingHomOfNhds f e s u) (f.fiberLift ht x) ≠ 0 := by
    refine fun t ht x ↦ ⟨fun ⟨y, hy, hxy⟩ ↦ ?_, fun hx ↦ ⟨f.fiberLift ht x, hx, ?_⟩⟩
    · have hyx : y = f.fiberLift ht x :=
        (f ⁻¹ᵁ V).ι.isEmbedding.injective (hxy.trans (f.fiberLift_apply ht x).symm)
      rwa [hyx] at hy
    · exact f.fiberLift_apply ht x
  -- the product does not vanish anywhere on the fibre over `t₀`, and `f` is a closed map, so the
  -- fibre over every nearby point is contained in `Ω` as well
  have htube : ∀ᶠ t in nhds t₀, ∀ w ∈ f.base ⁻¹' {t}, w ∈ Ω := by
    refine f.isClosedMap.eventually_nhds_fiber t₀ fun w hw ↦ hΩopen.mem_nhds ?_
    obtain ⟨x, rfl⟩ : ∃ x : f.fiber t₀, f.fiberι t₀ x = w := (f.range_fiberι t₀).ge hw
    exact (hmem _ hV x).2 (fiberMap_pairingHomOfNhds_ne_zero f e s u hV x
      (fiberMk_ne_zero_of_universallyClosed (f.fiberToSpecResidueField t₀) hLunit hs x)
      (fiberMk_ne_zero_of_universallyClosed (f.fiberToSpecResidueField t₀) hNunit hu x))
  filter_upwards [htube, V.isOpen.mem_nhds hV] with t ht htV
  -- the geometric integrality of the fibre over `t` is an instance for the criterion below
  have := hgeom t htV
  have : IsIntegral (f.fiber t) := GeometricallyIntegral.isIntegral (f.fiberToSpecResidueField t)
  obtain ⟨x⟩ : Nonempty (f.fiber t) := IsIntegral.nonempty
  have hne : fiberMap (pairingHomOfNhds f e s u) (f.fiberLift htV x) ≠ 0 :=
    (hmem t htV x).1 (ht _ (f.apply_fiberι t x))
  rw [nonempty_restrictToFiber_iso_structureModules_iff_nontrivial f e t]
  exact ⟨nontrivial_of_ne _ 0 fun h ↦
      hne (fiberMap_pairingHomOfNhds_eq_zero_of_left f e s u htV x h),
    nontrivial_of_ne _ 0 fun h ↦
      hne (fiberMap_pairingHomOfNhds_eq_zero_of_right f e s u htV x h)⟩

end NearPoint

section Projection

variable {X T : Scheme.{u}} {K : Type u} [Field K]

/-- **Formal triviality is triviality near the point.**

Let `X` be a proper geometrically integral variety over a field `K`, let `T` be a locally
Noetherian `K`-scheme, let `t₀` be a point of `T` and let `L` be a line bundle on `X × T` whose
pullback to `(X × T) ×_T Tₙ` is trivial for every `n`, where `Tₙ` is the `n`-th infinitesimal
neighbourhood of `t₀`. Then there is an open neighbourhood `V` of `t₀` such that the restriction
of `L` to the fibre `X_t` is trivial for every `t` in `V`.

This is `prop:cube-formal-triviality` of the blueprint. It rests on
`AlgebraicGeometry.Scheme.Modules.exists_fiberSectionsOfNhds_pullbackSnd_ne_zero`, which is
`sorry`-tainted by design, and is applied here once for `L` and once for its tensor inverse. -/
theorem exists_mem_forall_nonempty_restrictToFiber_pullbackSnd_iso_structureModules
    (πX : X ⟶ Spec (.of K)) [IsProper πX] [GeometricallyIntegral πX]
    (πT : T ⟶ Spec (.of K)) [IsLocallyNoetherian T] (t₀ : T)
    {L : (Limits.pullback πX πT).Modules} (hL : L.Invertible)
    (hF : ∀ n : ℕ, Nonempty
      ((pullback (infinitesimalBaseChangeFst (Limits.pullback.snd πX πT) t₀ n)).obj L ≅
        (infinitesimalBaseChange (Limits.pullback.snd πX πT) t₀ n).structureModules)) :
    ∃ V : T.Opens, t₀ ∈ V ∧ ∀ t ∈ V,
      Nonempty ((restrictToFiber (Limits.pullback.snd πX πT) t).obj L ≅
        ((Limits.pullback.snd πX πT).fiber t).structureModules) := by
  set f := Limits.pullback.snd πX πT
  set N : (Limits.pullback πX πT).Modules := hL.tensorInv with hNdef
  have hN : N.Invertible := hNdef ▸ SheafOfModules.invertible_tensorInv hL
  -- coherence of `L` and of `N` is an instance for `exists_fiberSectionsOfNhds_pullbackSnd_ne_zero`
  have : L.IsCoherent := hL.isCoherent
  have : N.IsCoherent := hN.isCoherent
  -- `N` is trivial on every infinitesimal neighbourhood, because `L` is
  have hFN : ∀ n : ℕ, Nonempty
      ((pullback (infinitesimalBaseChangeFst f t₀ n)).obj N ≅
        (infinitesimalBaseChange f t₀ n).structureModules) := fun n ↦
    ⟨isoStructureModulesOfTensorIso
      (Functor.Monoidal.mapIsoTensorUnit (pullback (infinitesimalBaseChangeFst f t₀ n))
        hL.tensorInvIso) (hF n).some⟩
  obtain ⟨V₁, hV₁, s, hs⟩ := exists_fiberSectionsOfNhds_pullbackSnd_ne_zero πX πT t₀ L hF
  obtain ⟨V₂, hV₂, u, hu⟩ := exists_fiberSectionsOfNhds_pullbackSnd_ne_zero πX πT t₀ N hFN
  have hev := eventually_nonempty_restrictToFiber_iso_structureModules f hL.tensorInvIso
    (V := V₁ ⊓ V₂) ⟨hV₁, hV₂⟩ (fun t _ ↦ inferInstance)
    (((pushforward f).obj L).presheaf.map (homOfLE inf_le_left).op s)
    (fun hz ↦ hs ((ConcreteCategory.congr_hom (map_comp_fiberSectionsOfNhds f L hV₁ inf_le_left
      ⟨hV₁, hV₂⟩) s).symm.trans ((ConcreteCategory.comp_apply _ _ s).trans hz)))
    (((pushforward f).obj N).presheaf.map (homOfLE inf_le_right).op u)
    (fun hz ↦ hu ((ConcreteCategory.congr_hom (map_comp_fiberSectionsOfNhds f N hV₂ inf_le_right
      ⟨hV₁, hV₂⟩) u).symm.trans ((ConcreteCategory.comp_apply _ _ u).trans hz)))
  obtain ⟨S, hSsub, hSopen, hSmem⟩ := mem_nhds_iff.1 hev
  exact ⟨⟨S, hSopen⟩, hSmem, fun t ht ↦ hSsub ht⟩

end Projection

end

end Modules

end AlgebraicGeometry.Scheme
