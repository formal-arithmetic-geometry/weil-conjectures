1. Files written:
- `lem-sc-finite-flat-unramified-tangent-criterion.json`: split item with three proof steps.
- `lem-sc-rational-unramified-cotangent-criterion.json`: statement-only intermediate node; Mathlib search verdict no match.
- `citations.json`: verbatim statement quotes for all cited nodes.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof and its source description compressed three distinct arguments. I checked the parent node `lem-sc-mult-n-etale-kernel` and its proof step (b), then read the existing tangent/cotangent duality and linear-duality nodes. The new node records the local Stacks criterion that unramifiedness at a rational point is equivalent to surjectivity on maximal ideals modulo squares; no duplicate node or blueprint statement was found. The Mathlib searches for the item and new node were run with `msearch.py`; LeanSearch was unavailable for the new node's search, while LeanFinder and grep returned no scheme-point tangent criterion. No sorry-free Lean declaration tagged with the item ID or stating the criterion was found.

## Review by G1
I read the item source metadata in `varieties.tex`, the parent proof in `lem-sc-mult-n-etale-kernel.json`, and the statements of `lem-sc-rational-tangent-cotangent-duality`, `lem-sc-dual-map-injective-iff-surjective`, and `lem-weil-pbc-local-flat-unramified-etale`. Step 1 uses the first node for the exact duality assertion and the second for injective-dual versus surjective-original; the rationality hypotheses are exactly those required by the duality node. Step 2 uses the new node verbatim, with the same closed rational points and cotangent spaces. Step 3 checks that finite locally free implies flat and locally finitely presented, then invokes the local flat-unramified-etale criterion. I tested the statement on the identity map (both conditions hold), on `Spec(k[ε]/(ε²)) -> Spec k` (neither holds), and on a separable finite field extension at a rational point (the tangent spaces are zero and the map is etale). The only correction to the imported item was supplying the missing proof and isolating the local unramified cotangent criterion as a statement-only dependency.

5. What I could not finish: no Lean compilation is permitted in stage 1; the dry run is the remaining verification step.

## Second reading by G1
Step 1 checked against `lem-sc-rational-tangent-cotangent-duality` and `lem-sc-dual-map-injective-iff-surjective`; the cited statements give exactly the tangent/cotangent duality and injective-dual/surjective equivalence under the rationality hypotheses; verdict: sound.
Step 2 checked against `lem-sc-rational-unramified-cotangent-criterion`; its statement is the required local finite-type rational-point criterion; verdict: sound, with the source proof located at Varieties Tag 0B2G and the differential exact sequence/local unramified criterion.
Step 3 checked against `def-pc-finite-locally-free` and `def-weil-etale-morphism`; finite locally free supplies flatness and local finite presentation, so etale is equivalent to unramified; verdict: repaired and sound.
`lem-sc-rational-unramified-cotangent-criterion` checked for B1--B7, source hypothesis-by-hypothesis against Varieties Tag 0B2G and the local characterization of unramifiedness; tested on the identity, dual-number thickening, and separable field extension; verdict: valid statement-only dependency, no existing duplicate found by DAG and Mathlib searches.

Changes: removed the mismatched `lem-weil-pbc-local-flat-unramified-etale` dependency from the item statement and proof; added the finite-locally-free, tangent-space, and etale definition dependencies; rewrote Step 3 as the direct definitional argument and marked it elementary; updated proof dependencies accordingly. No source statement was changed.
