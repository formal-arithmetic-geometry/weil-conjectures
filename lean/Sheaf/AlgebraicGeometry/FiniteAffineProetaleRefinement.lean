module

public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Finite affine refinement of a pro-etale cover

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-ctf.proof.md`, Step (2), Local models
(blueprint: lem-sfb-finite-affine-proetale-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Finite affine refinement of a covering family in the small pro-etale site.

Source: `det-prop-scalar-six-ctf.proof.md`, Step (2), Local models: finite affine
refinement and verification that the finite family is a pro-etale cover
(blueprint: lem-sfb-finite-affine-proetale-refinement).

The given covering family `{W_i → S}` is `𝒰 : S.Cover Scheme.proetalePrecoverage`; the
finite affine open cover is `U : Fin t → S.Opens`.  The finite family `{V α j → S}` is indexed
by `Σ α : Fin t, Fin (n α)`; the last conjunct is the finite (quasi-compact open) refinement
condition of `sk-def-pe-site` over every affine open `W ⊆ S`, written for the base changes
`V α j ×_S W → W`, exactly as in `QuasiCompactCover`.

Proof:

1. Pull the quasi-compact cover back to each affine `U α` and apply
   `QuasiCompactCover.exists_isAffineOpen_of_isCompact` to its whole space. This gives
   the finite affine opens and their covering equalities.
2. The selected maps to `S` are weakly etale: they compose an open immersion, the base
   change of the open immersion `U α → S`, and a member of the original cover.
   Mathlib's weakly etale instances prove this directly.
3. The pullback identity shows that the selected images cover `S`, using the given
   cover by the `U α`. Every selected source is affine, hence quasi-compact; since `S`
   is quasi-separated, its map to `S` is quasi-compact
   (`lem-weil-pbc-qcqs-morphism-permanence` (1)). After base change to an affine `W`,
   these maps are still quasi-compact, as is `W → S`.
4. The composites from the base changes to `S` are spectral. Their images cover `W`
   by `Scheme.Pullback.exists_preimage_pullback`. The finite-family lemma
   `IsCompactOpenCovered.of_finite_of_isSpectralMap` now gives the final clause:
   explicitly, the whole base changes are compact opens with images covering `W`.
   No auxiliary affine cover of the intersections `W ∩ U α` is needed.
-/
theorem finite_affine_proetale_refinement
    (S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S]
    [QuasiSeparatedSpace S]
    (𝒰 : S.Cover Scheme.proetalePrecoverage)
    (t : ℕ) (U : Fin t → S.Opens)
    (hU_affine : ∀ α, IsAffineOpen (U α))
    (hU_cover : ⋃ α, (U α : Set S) = Set.univ) :
    ∃ (n : Fin t → ℕ)
      (i : ∀ α, Fin (n α) → 𝒰.I₀)
      (V : ∀ α j, (pullback (𝒰.f (i α j)) (U α).ι).Opens),
      (∀ α j, IsAffineOpen (V α j)) ∧
      (∀ α, ⋃ j, Set.range
          (((V α j).ι ≫ pullback.snd (𝒰.f (i α j)) (U α).ι).base) =
        (Set.univ : Set (U α).toScheme)) ∧
      (∀ α j, WeaklyEtale
          ((V α j).ι ≫ pullback.fst (𝒰.f (i α j)) (U α).ι ≫ 𝒰.f (i α j))) ∧
      (∀ (W : S.Opens), IsAffineOpen W →
        IsCompactOpenCovered
          (fun p : Σ α : Fin t, Fin (n α) ↦
            (pullback.snd
              (((V p.1 p.2).ι ≫
                pullback.fst (𝒰.f (i p.1 p.2)) (U p.1).ι ≫
                𝒰.f (i p.1 p.2))) W.ι ≫ W.ι).base)
          (W : Set S)) := by
  classical
  -- Refine the pullback cover over each affine member of the fixed open cover.
  have hlocal (α : Fin t) :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact
      (𝒰.toPreZeroHypercover.pullback₂ (U α).ι)
      (U := ⊤) (by
        have : IsAffine (U α).toScheme := hU_affine α
        exact isCompact_univ)
  dsimp only [PreZeroHypercover.pullback₂] at hlocal
  choose n i V hV hcov using hlocal
  have hrange (α : Fin t) :
      ⋃ j, Set.range (((V α j).ι ≫
        pullback.snd (𝒰.f (i α j)) (U α).ι).base) =
        (Set.univ : Set (U α).toScheme) := by
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_top] using hcov α
  have hweak (α : Fin t) (j : Fin (n α)) : WeaklyEtale
      ((V α j).ι ≫ pullback.fst (𝒰.f (i α j)) (U α).ι ≫ 𝒰.f (i α j)) := by
    have : WeaklyEtale (𝒰.f (i α j)) := 𝒰.forgetQc.map_prop _
    infer_instance
  refine ⟨n, i, V, hV, hrange, hweak, ?_⟩
  let f (p : Σ α : Fin t, Fin (n α)) : (V p.1 p.2).toScheme ⟶ S :=
    (V p.1 p.2).ι ≫ pullback.fst (𝒰.f (i p.1 p.2)) (U p.1).ι ≫ 𝒰.f (i p.1 p.2)
  -- Affine sources and a quasi-separated target make these maps quasi-compact.
  have haff (p : Σ α : Fin t, Fin (n α)) : IsAffine (V p.1 p.2).toScheme :=
    hV p.1 p.2
  have hsurj (x : S) : ∃ p, x ∈ Set.range (f p).base := by
    have hx : x ∈ ⋃ α, (U α : Set S) := hU_cover.symm ▸ Set.mem_univ x
    obtain ⟨α, hα⟩ := Set.mem_iUnion.mp hx
    have hy : (⟨x, hα⟩ : (U α).toScheme) ∈
        ⋃ j, Set.range (((V α j).ι ≫
          pullback.snd (𝒰.f (i α j)) (U α).ι).base) :=
      (hrange α).symm ▸ Set.mem_univ _
    obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hy
    refine ⟨⟨α, j⟩, y, ?_⟩
    change ((V α j).ι ≫ pullback.fst _ _ ≫ 𝒰.f _) y = x
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (fun z : (U α).toScheme ↦ z.1) hy
  intro W hW
  have : IsAffine W.toScheme := hW
  -- A finite spectral family covering the compact open W gives its fpqc condition.
  apply IsCompactOpenCovered.of_finite_of_isSpectralMap
    (fun p ↦ (pullback.snd (f p) W.ι ≫ W.ι).isSpectralMap)
    (hU := W.isOpen) (hc := hW.isCompact)
  intro x hx
  obtain ⟨p, y, hy⟩ := hsurj x
  obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := f p) (g := W.ι)
    y (⟨x, hx⟩ : W.toScheme) hy
  exact ⟨p, z, congrArg (fun z : W.toScheme ↦ z.1) hz⟩

end AlgebraicGeometry
