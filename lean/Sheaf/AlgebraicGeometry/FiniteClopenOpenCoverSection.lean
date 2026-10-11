/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits

/-!
# A finite surjective disjoint union of open immersions has a section

Source: literature/stacks-project/etale-cohomology.tex, Lemma 59.80.6 (Tag 09ZA),
proof, final paragraph (blueprint: lem-weil-pbc-clopen-open-cover-section).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: literature/stacks-project/etale-cohomology.tex, Lemma 59.80.6 (Tag 09ZA),
proof, final paragraph (blueprint: lem-weil-pbc-clopen-open-cover-section).

The finite coproduct decomposition is represented by a finite index `Fin n`, with
open-and-closed coproduct injections `k`; the restrictions of `p` are the morphisms
`pᵢ`, each an open immersion. The conclusion is a section of `p`.

Proof:
1. Put `Uᵢ = pᵢ(Vᵢ)`. These images are open by
   [def-weil-open-immersion], and closed because `p` is a closed map by
   [lem-weil-pbc-finite-closed-map-finite-fibres] and each `Vᵢ` is closed in `V`.
   They cover `Z` by [def-weil-surjective-morphism] and the coproduct decomposition.
2. For each nonempty subset `A` of the indices, take the intersection of the `Uᵢ`
   for `i ∈ A` and their complements for `i ∉ A`. These finite intersections are
   clopen, pairwise disjoint, and cover `Z`: a point belongs to the unique stratum
   indexed by the nonempty set of images containing it. Choose the least index in
   `A`; its image contains that stratum. Empty strata cause no difficulty.
3. By [lem-weil-pbc-open-immersion-iso-onto-image], the chosen `pᵢ` identifies `Vᵢ`
   with `Uᵢ`. Factor the stratum inclusion through `Uᵢ` using
   [lem-weil-pbc-morphism-factors-through-open-subscheme], compose with the inverse
   of this isomorphism and then with `kᵢ`. Its composite with `p` is the stratum
   inclusion.
4. These local sections agree on overlaps, which are empty for distinct strata;
   the empty scheme has a unique morphism to `V`. Glue them using
   [lem-weil-pbc-scheme-morphism-gluing]. The composite with `p` restricts to the
   identity on every stratum, hence equals the identity by uniqueness of gluing.
-/
theorem exists_section_of_finite_clopen_open_cover
    {n : ℕ} (Z V : Scheme.{u}) (p : V ⟶ Z)
    [IsFinite p] [Surjective p]
    (Vi : Fin n → Scheme.{u})
    (k : ∀ i, Vi i ⟶ V)
    (hk : ∀ i, IsOpenImmersion (k i) ∧ IsClosedImmersion (k i))
    (hcop : IsColimit (Cofan.mk V k))
    (pi : ∀ i, Vi i ⟶ Z)
    (hpi : ∀ i, pi i = k i ≫ p)
    [∀ i, IsOpenImmersion (pi i)] :
    ∃ s : Z ⟶ V, s ≫ p = 𝟙 Z := by
  sorry

end AlgebraicGeometry
