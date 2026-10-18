module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability

/-!
# Finite affine refinement of a pro-etale cover

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-ctf.proof.md`, Step (2), Local models
(blueprint: lem-sfb-finite-affine-proetale-refinement).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

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

Proof (node proof, steps 1--5):

1. Each affine open `U α → S` is an object of the small pro-etale site. The covering clause
   of `sk-def-pe-site` for `{W_i → S}` and the affine open `U α` gives finitely many indices
   `i α j` and affine opens `V α j ⊆ W_{i α j} ×_S U α` whose images cover `U α`.
2. Each `W_i → S` is weakly etale (object clause of `sk-def-pe-site`). Base change along
   `U α → S` preserves weak etaleness (`sk-lem-pe-weakly-etale-stability`), so
   `W_i ×_S U α → U α` is weakly etale; its restriction to the affine open `V α j` is weakly
   etale by locality on the source. The open immersion `U α → S` is weakly etale as the
   restriction of `id_S` (flat with isomorphic diagonal, `sk-def-pe-morphisms`) to an open,
   so the composite is weakly etale by the composition clause. The fibre-product universal
   property (`def-pc-fibre-product`) identifies it with `V α j → W_{i α j} → S`.
3. Let `W ⊆ S` be an affine open. As `S` is quasi-separated, each `W ∩ U α` is quasi-compact
   (`lem-weil-pbc-quasi-separated-affine-cover-criterion` (1)), hence covered by finitely
   many affine opens `A α k` (`lem-weil-pbc-qcqs-finite-affine-open-cover`); as the `U α`
   cover `S`, the finitely many `A α k` cover `W`.
4. For each `A α k` and each `V α j`, the fibre product `V α j ×_{U α} A α k` of affine
   schemes over the affine `U α` is affine (`lem-weil-pbc-fibre-product-affine-spectra`).
   Since `A α k ⊆ W ∩ U α` and `U α → S` is an open immersion, `def-pc-fibre-product`
   identifies it with `V α j ×_S A α k`, the open subscheme of `V α j ×_S W` over `A α k`.
   Its image in `A α k` is the intersection of the image of `V α j` with `A α k`; as the
   images of the `V α j` cover `U α ⊇ A α k`, these finitely many affine opens have images
   covering `A α k`. The finite union over `α, k, j` covers `W`.
5. The covering condition of `sk-def-pe-site` for `{V α j → S}` is exactly what Step 4
   verifies for every affine open `W ⊆ S`, and Step 2 gives weak etaleness of every member.
   So the finite family is a covering family of `S_proet`; its index set is finite because
   the affine cover and each local refinement are finite.
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
  sorry

end AlgebraicGeometry
