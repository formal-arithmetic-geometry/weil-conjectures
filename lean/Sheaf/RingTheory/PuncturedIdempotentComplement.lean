module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.RingTheory.CoverModuleExact

/-!
# Complementary quotient for idempotent localizations off a finitely generated ideal

Source: Stacks Project, More on Algebra, Tag 0C2A,
`lemma-glueing-sum-components-open` (blueprint: lem-per-punctured-idempotent-complement).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A ring map which is localization at an idempotent off a finitely generated ideal
has a surjective complementary ring map whose product is an isomorphism there.
Source: Stacks Project, More on Algebra, Tag 0C2A,
`lemma-glueing-sum-components-open` (blueprint: lem-per-punctured-idempotent-complement).

The algebra structure in `hlocal` is explicitly induced by `Localization.awayMap u f`;
thus the hypothesis identifies the given map, including its action on scalars.
Bijectivity in the conclusion says that the specified product-localization map is a
ring isomorphism. The complementary ring can be taken in the universe of `R`, as a quotient.

Proof:
1. Choose a finite generating list `f_i` of `K`. If the list is empty, `K = 0`;
   take `E' = R` and `v` the identity. The only required localization is at zero,
   and both its source and target are zero rings
   (`def-weil-ring-localization-away`).
2. Write each local idempotent as `a_i / f_i^n`, choosing a common exponent and
   clearing the idempotence relations so that `a_i^2 = f_i^n * a_i` in `R`.
   This uses the fraction equality of `def-weil-ring-localization-away`.
3. On each overlap the two localizations identify the same structural map with
   localization at either idempotent. Each idempotent becomes one after inverting
   the other. The zero-fraction criterion gives both `e_i * e_j = e_i` and
   `e_i * e_j = e_j`, so the idempotents agree on the overlap.
4. Clear these finitely many overlap equalities with one exponent `N`. Replacing
   `a_i` by `b_i = f_i^N * a_i` and setting `d = n + N` gives
   `f_j^d * b_i = f_i^d * b_j`, `b_i^2 = f_i^d * b_i`, and `e_i = b_i / f_i^d`.
   Thus every `b_j` belongs to the ideal of `b_i` after inverting `f_i`.
5. Set `J = (b_1, ..., b_r)`, `E' = R / J`, and take the quotient map `v`.
   Then `J R_{f_i} = (e_i)`. By `lem-weil-pbc-localization-quotient-commute`,
   the localization of `E'` at `v(f_i)` is `R_{f_i} / (e_i)` compatibly with `v`.
6. For any idempotent `e` of a ring `B`, the canonical map
   `B -> B_e × B/(e)` is an isomorphism: identify its factors with `eB` and
   `(1-e)B`. The inverse to `b -> (eb, (1-e)b)` is addition.
   Applying this with `B = R_{f_i}` proves the desired decomposition at each generator.
7. Localization commutes with the two-factor product: its comparison sends
   `(x,y)/f^k` to `(x/f^k,y/f^k)`; the inverse sends `(x/f^k,y/f^l)` to
   `(f^l*x,f^k*y)/f^(k+l)`. The fraction equality checks both inverses.
   Consequently step 6 proves bijectivity of exactly `Localization.awayMap (u.prod v) f_i`.
   Further localization preserves this bijectivity.
8. For any `f` in `K`, the images of the `f_i` generate the unit ideal of `R_f`.
   Use `lem-weil-pbc-cover-module-exact` on these images. Injectivity is checked
   on that cover; local preimages of any target element agree on overlaps by
   injectivity there, so the gluing clause supplies a global preimage. The same
   cover's injectivity clause in the target verifies that this preimage maps to
   the original element. Module and ring localizations agree by their fraction
   constructions (`def-weil-pbc-module-localization-away` and
   `def-weil-ring-localization-away`). Hence the product map is bijective for every `f` in `K`.
-/
theorem exists_surjective_complement_of_localization_idempotent
    {R : Type u} [CommRing R] {E : Type v} [CommRing E]
    (K : Ideal R) (hK : K.FG) (u : R →+* E)
    (hlocal : ∀ f ∈ K, ∃ e : Localization.Away f, IsIdempotentElem e ∧
      @IsLocalization.Away (Localization.Away f) _ e (Localization.Away (u f)) _
        (Localization.awayMap u f).toAlgebra) :
    ∃ (E' : Type u) (_ : CommRing E') (v : R →+* E'),
      Function.Surjective v ∧ ∀ f ∈ K,
        Function.Bijective (Localization.awayMap (u.prod v) f) := by
  sorry

end RingHom
