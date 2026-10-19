1. Files written:

- `dag/nodes/sec-six-functors/lem-coef-kan-quillen-cartesian-pushout-product.json` — statement, split proof, and citations; no Mathlib match for the whole result.
- `dag/nodes/sec-six-functors/lem-coef-kan-quillen-pushout-product-weak-equivalence.json` — statement-only helper; Mathlib searches found no exact match.
- `citations.json` — verbatim citations for every non-elementary dependency of the item proof.

2. Attachments: none.

3. WANTED: Hovey, *Model Categories*, the Kan–Quillen cartesian monoidal model-structure/pushout-product argument (the repository item cites this source but has no archival copy).

4. No statement error was found. The item uses the small simplicial sets and weak homotopy equivalences supplied by `lem-coef-kan-quillen-right-proper`. The existing `lem-coef-sset-anodyne-pushout-product` is relevant only to the horn case, so I did not duplicate it. The new helper is strictly more general than the item's weak-equivalence clause: it allows an arbitrary monomorphism in the first variable, whereas the item restricts that variable to a boundary or horn generator. It was created because the current DAG and Mathlib contain no node stating the cartesian Kan–Quillen pushout-product axiom.

## Not duplicates

- `lem-coef-kan-quillen-pushout-product-weak-equivalence` vs `lem-coef-sset-anodyne-pushout-product`: the existing node proves anodyne-ness when one factor is anodyne; the new node proves weak homotopy equivalence for an arbitrary weak-equivalence factor and does not assume anodyne-ness.
- `lem-coef-kan-quillen-pushout-product-weak-equivalence` vs `lem-coef-joyal-cartesian-pushout-product`: the latter concerns categorical equivalences in the Joyal structure; the new node concerns weak homotopy equivalences in the Kan–Quillen structure.

5. What I could not finish: no source copy of Hovey was available in `literature/`, so the proof origin is recorded as an agent reconstruction with the requested WANTED entry. No Lean source declaration was found for the item, and no compiler or build was run.

## Review by NI

I read the imported item node, the `sec-six-functors` chapter record, and unit `sk-prop-sf-biduality-general`, then checked the ancestor blueprint place in `prop-coef-integral-exceptional-adjoint`. I searched the full DAG and blueprint for cartesian pushout-product, anodyne pushout-product, and Kan–Quillen weak-equivalence statements. The existing anodyne leaf states exactly the lifting result needed after swapping the two Cartesian factors; it does not state weak homotopy equivalence for an arbitrary weak-equivalence factor. The right-proper node states that Kan fibrations are the fibrations in the Kan–Quillen model structure and that its weak equivalences are the stated geometric-realization weak homotopy equivalences.

For Step 1 I checked the degreewise set pushout: the two summand images meet in the image of (P\times K), so injectivity follows from the injectivity of (i) and (j). For Step 2 I verified that a horn has the left lifting property against every Kan fibration by definition, that the cited anodyne node applies to (j\square i), and that the coordinate flips identify this pushout with (i\square j). The right-proper model-structure statement then converts the lifting class into trivial cofibrations and hence weak homotopy equivalences. For Step 3 I checked that the new helper applies with (a=i) and (b=j), since (i) is a monomorphism and (j) is a weak homotopy equivalence. I tested the edge cases (m=0), the empty simplicial set, identity (j), and the smallest horn (Lambda^1_k\hookrightarrow\Delta^1); the set-union and symmetry arguments remain valid. Every non-elementary citation is represented by a verbatim quote in `citations.json`.
