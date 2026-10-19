# Stage-1 report: lem-sf-strict-roos-derived-limit-comparison

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-strict-roos-derived-limit-comparison.json`: existing item, split into four proof steps; no new nodes.
- `citations.json`: 10 verbatim node-statement quotations covering all step dependencies.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id and for strict-Roos, homotopy-limit, and derived-limit comparison declarations. No sorry-free project declaration states this item exactly.

## WANTED

None.

## Not duplicates

- `lem-sf-strict-roos-derived-limit-comparison` vs `lem-weil-strict-roos-comparison`: the existing node gives the functorial product-cone comparison and injective-term normalization, while this item specializes it to the signed Roos complex of an arbitrary K-injective tower resolution and adds the explicit evaluation maps.
- `lem-sf-strict-roos-derived-limit-comparison` vs `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: the existing node supplies the total derived inverse-limit functor and its abstract Roos triangle/pro-zero property; this item identifies the concrete chain-level Roos cone with that functor and normalizes every evaluation.
- `lem-sf-strict-roos-derived-limit-comparison` vs `lem-weil-pbc-sequential-tower-evaluation-full`: that node lifts compatible morphisms between derived evaluations to a strict tower map; this item compares a fixed tower resolution with its total inverse limit and does not assert fullness of the evaluation functor.

## Review by Q138

I read the imported item node, `def-weil-rationalization-karoubi` in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sf-operations/`, and the current unit/chapter records. The item’s hypotheses and conclusions were retained verbatim. The source search found no project declaration carrying the blueprint tag or an exact strict-Roos comparison theorem.

I read the complete statements of `lem-weil-strict-roos-comparison`, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, `lem-weil-tower-category-levelwise-abelian`, `lem-weil-pbc-small-module-diagrams-grothendieck`, `lem-pur-kinjective-degreewise-existence`, and `lem-weil-pbc-kinjective-hom-derived`. The proof cites only what those statements provide. In particular, the first existing node explicitly supplies a functor on the derived tower category and its injective-term normalization; the ringed strict-tower node explicitly says that total derived inverse limit is computed by a K-injective tower resolution followed by termwise limit; the functor-category node supplies levelwise exactness; and the K-injective Hom node supplies homotopy equivalences between quasi-isomorphic K-injectives.

Step 1 checks the sign convention: the item’s ordered pair `(y,x)` is the shifted-product coordinate followed by the product coordinate, so the differential is exactly `(-dy-(1-s)x,dx)`. The tower-map equation makes the two product maps commute with the shift, and exact evaluation makes the resolution map a quasi-isomorphism. Step 2 replaces the arbitrary resolution by the functorial injective-term K-injective resolution in the Grothendieck tower category and invokes the existing node’s canonical inclusion `lim J -> C(J)`. Step 3 applies the homotopy inverse termwise to the limit and writes the chain-level square `C(v) η_I = η_J L(v)`; this proves the inclusion for the original arbitrary K-injective resolution rather than silently assuming injective terms. Step 4 uses the strict total-limit node to identify `L_I` with `R lim X`, and computes both evaluation identities directly: `a_n^I η_I = p_n` and `a_n^I C(u)=u_n a_n^X`. Exact evaluation verifies that the specified derived evaluation is `u_n^{-1}p_n`, giving `e_n θ=a_n^X`.

I tested the construction on the zero tower, a constant identity tower, and a tower with all transitions zero. The zero and constant cases reduce to the expected zero and constant product-cone fibers; the zero-transition case has `1-s=1` and hence zero derived limit. The proof steps are each under 2000 characters and contain no hidden auxiliary lemma. No SGA source is used. The recorded searches were run through `msearch.py`; LeanFinder and LeanSearch returned only generic limit/cone or quasi-isomorphism declarations, grep returned no Roos/derived-inverse-limit match, and the invalid Loogle identifier was recorded as unavailable rather than as a negative result.

## Problems and corrections

No statement dispute was found. The original empty proof lacked the extension from injective-term resolutions to an arbitrary K-injective resolution. The four steps now supply that extension explicitly. The source field correctly distinguishes the agent-written normalization from Stacks’ abstract derived-limit statement. No source, unit, or chapter error is claimed.

## Unfinished work

None in this one-level split. Existing cited prerequisites retain their current DAG states and are not edited.
