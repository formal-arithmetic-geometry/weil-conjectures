# Stage 1 report: lem-coef-active-operad-envelope-cocartesian

## Files written

- `dag/nodes/sec-six-functors/lem-coef-active-operad-envelope-cocartesian.json`: item marked `split`; the existing eight-step proof and blueprint metadata were retained.
- No new node files: the proof's helper nodes `lem-coef-infinity-lax-comma-target-fibration` and `lem-coef-operadic-inert-active-factorization`, together with the remaining dependencies, already exist in the shared DAG and were cited by their exact ids.
- `citations.json`: 30 step/node entries, each quoting the complete statement of the cited node verbatim.

## Attachments

No finished, sorry-free declaration matching the item was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; no attachment is claimed.

## WANTED

- Lurie, *Higher Topos Theory* (HTT), Corollaries 2.4.7.11–12 and Proposition 2.4.4.3 (archived copy for `lem-coef-infinity-lax-comma-target-fibration`, `def-coef-infinity-fibrations`, and `lem-coef-infinity-cocartesian-mapping-criterion`).
- Lurie, *Higher Algebra* (HA), Definitions 2.1.2.10, 2.3.3.6/25, Theorems 2.3.3.23/26, Proposition 2.1.2.4–5, Construction 2.2.4.1 and Proposition 2.2.4.4 (archived copy for `lem-coef-operadic-approximation-restriction`, `lem-coef-operadic-inert-active-factorization`, and this item).
- Kerodon, Subsection 4.6.4, Proposition 3.4.1.11 (tag 0110), Subsection 4.6.8, and Theorem 4.8.4.1 (tags 01KE, 01PF, 01JX) for the mapping-space, pasting, composition, and essential-image statements.

## Review by Q14

I checked the item statement against the HA construction and proposition cited in its `source`: it introduces the full active-arrow subcategory of the pullback, uses the stated inner-fibration and equivalence-lifting hypotheses on `p`, and concludes exactly that the target evaluation is an inert-preserving cocartesian fibration of symmetric infinity-operads with the stated edge criterion. The Lean source search found no declaration carrying the blueprint tag or an exact theorem, so the item remains a natural-language split.

For step 1 I read the statement of `lem-coef-infinity-lax-comma-target-fibration` (the unrestricted arrow pullback is a quasicategory, target evaluation is cocartesian, and its mapping-space homotopy pullback has the two specified composites) and `def-coef-infinity-fibrations` (inner and cocartesian fibration notions). Those statements justify restricting to the full active subcategory and the displayed mapping formula. Step 2 uses the cited `lem-coef-operadic-approximation-restriction` definition of the operadic structure, `lem-coef-infinity-cocartesian-mapping-criterion`'s mapping criterion, `lem-coef-infinity-homotopy-pullback-pasting`'s transitivity of path-space pullbacks, and `lem-coef-operadic-inert-active-factorization`'s inert/active factorization and orthogonality. I checked that the source component is inert, that the equivalence-lifting hypothesis is used to obtain an exact inert lift, and that the comparison equivalence is in the correct direction.

Step 3 was checked against the same comma mapping formula, the inert/active orthogonality statement, the cocartesian mapping criterion, and homotopy-pullback pasting: the diagonal filler space supplies the entire homotopy pullback, not merely a component-level lift. Step 4 uses the factorization, mapping criterion, `lem-coef-infinity-mapping-composition` for composition and equivalences, and the lax-comma statement; I verified the constructed lift exists for every target arrow and that comparison of two universal lifts proves the converse inertness claim. Step 5 uses the operadic approximation/restriction statement, cocartesian mapping criterion, pasting, inert/active factorization, and `lem-coef-cocartesian-straightening`; I checked inert pointed maps, preservation under `r`, and the restriction/straightening assertion.

For step 6 I checked the finite pointed-set partition and empty-block/nullary cases against the operadic factorization, mapping criterion, comma, and approximation statements. Step 7 uses the comma mapping formula and operadic approximation/restriction; I verified the index bijection `alpha v = u beta`, the product of homotopy pullbacks, dropped inputs, and the zero-output case. Step 8 uses the approximation/restriction, comma, mapping criterion, straightening, and `lem-coef-infinity-full-essential-image`; I checked the identification of the fiber mapping spaces under the cocartesian projections, assembly of colorwise objects, essential surjectivity, and the empty family. Every cited node's statement was read from the shared DAG and is quoted verbatim in `citations.json`; every proof step's `uses` agrees with those quotes and with `proof_deps`.

I searched the whole DAG and blueprint for the item and for the two auxiliary constructions before reusing them. The existing helper nodes are strictly smaller statements and do not restate an item clause; no duplicate or cycle was introduced. I tested the proof's stated edge cases (empty source, arity zero/nullary operations, pointed permutations/equivalences, and empty blocks) while checking the steps. No statement or hypothesis was changed.

## Source error

None found.

## What remains

The cited HA, HTT, and Kerodon sources are online references rather than archived files, as recorded under `WANTED`; this is a documentation limitation only. No Lean files were written and no compiler or build tool was run.
