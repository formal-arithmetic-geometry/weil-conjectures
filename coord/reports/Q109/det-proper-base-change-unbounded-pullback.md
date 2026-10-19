# Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/det-proper-base-change-unbounded-pullback.json` — existing item split retained; no new nodes and no Mathlib leaves.
- `citations.json` — verbatim statements for every node used by every proof step.

Attachments: none. The source checkout contains no sorry-free declaration tagged `(blueprint: det-proper-base-change-unbounded-pullback)`.

WANTED: none.

The retained split follows the current main-20261015 blueprint proof. I checked the statement against the blueprint node and the current field-setting and coefficient conventions. The item is a statement node, so no new definition or lemma node was created. All cited nodes already exist in the DAG; no duplicate node was introduced. The retained proof's finite-coefficient paragraph expands the flat-model construction, while the general bounded-constructible pullback result is also available as `lem-sfb-dc-upper-star-preserves`; this is consistent with the unit's finite-flat-model route and does not alter the statement. No source error was found, and no proof obligation remains in this stage-1 split.

## Review by Q109

I read the item source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-proper-base-change-unbounded/sk-prop-proper-base-change-unbounded-pullback.md`, the corresponding proof file, the unit record `sk-prop-proper-base-change-unbounded.json`, and the current statements of every cited node. The item hypotheses are the distinct primes, characteristic-​`p` field, separated finite-type `k`-schemes and `k`-morphism, all admissible condensed coefficients (including the finite-subextension convention for `Q̄_ℓ`), the unbounded module derived categories, and the `Dctf`/localizing-closure definitions; these match the current blueprint and the standing setting.

Step 1 uses the statements of `sk-prop-sfb-cartesian-coefficients` for the coefficient isomorphism and exact module pullback, `lem-weil-pbc-exact-functor-derived-factorization` for the termwise exact derived functor, `sk-def-sfb-derived-categories` for exact-derived computation, `sk-def-sfb-module-derived-pushpull` for the derived pullback and adjunction, `lem-weil-pbc-left-adjoint-preserves-colimits` for coproduct preservation, `lem-pur-ringed-site-grothendieck-abelian` and `lem-kun-grothendieck-derived-coproducts` for existence of ambient derived coproducts, and `sk-def-localizing-closure` for the fixed small-universe localizing category. Each cited statement supplies the exact fact used.

Step 2 uses `lem-sfb-dc-upper-star-preserves` for bounded constructibility, `sk-def-sfb-dc-setting` and `sk-def-sfb-constructible` for the setting and Tor-amplitude predicate, `lem-pur-ringed-site-grothendieck-abelian`, `lem-pc-sheaf-modules-tensor-closed`, `lem-pc-kflat-bounded-flat-replacement`, and `lem-sc-source-tor-amplitude-flat-model` for the flat-model construction, `lem-pc-bounded-above-flat-kflat-site` for K-flatness, `def-weil-proetale-inverse-image` and `sk-prop-sfb-cartesian-coefficients` for the ringed-topos map and coefficient comparison, `lem-weil-pbc-ringed-topos-kflat-pullback` for preservation of flat terms and K-flatness, and `sk-def-sfb-derived-tensor-hom` for the tensor test. The hypotheses are checked at the finite coefficient ring `A`, with the bounded Tor interval `[a,b]`; the target module `N` is arbitrary, so the finite Tor conclusion is the stated one.

Step 3 uses `det-def-localizing-closure-ctf-equals-bc` only for the five integral/field coefficient cases, `sk-def-sfb-dc-setting` and `sk-def-sfb-dc-restricted-functors` for their preservation theorem, `def-weil-finite-type-morphism` for quasi-compactness, `def-weil-proper-morphism` and `lem-weil-pbc-proper-fp-permanence` for quasi-separatedness through the separated diagonal, and retains the uncompleted ambient pullback. The finite coefficient case is not silently generalized to these rings; the coefficient split is explicit.

Step 4 applies exactly the hypotheses and conclusion of `det-proper-image-localizing-principle`: exactness and coproduct preservation from Step 1 and generator preservation from Steps 2–3. The edge cases checked were the zero complex, an empty scheme, the empty coproduct, the field coefficient case, and the finite ring `Z/ℓ²` with the two-term multiplication-by-`ℓ` complex. I also checked that the Q̄_ℓ coefficient is the finite-subextension-valued condensed ring throughout and that no SGA source is cited. The long finite-coefficient step is a single flat-model and Tor-amplitude argument; its subclaims are all tied to the cited statements above.

No files outside this item sandbox were changed. No Lean source or compiler was used.

## Not duplicates

`det-proper-base-change-unbounded-pullback` vs existing `lem-sfb-dc-upper-star-preserves`: the existing node states bounded-constructibility preservation only; this item additionally proves exactness, all small coproducts, finite Tor-amplitude preservation, and restriction to the localizing closures.
