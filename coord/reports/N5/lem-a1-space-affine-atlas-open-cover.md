# Stage-1 delivery: lem-a1-space-affine-atlas-open-cover

## 1. Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-space-affine-atlas-open-cover.json`: existing statement, now split into four steps. The statement and its statement dependencies are unchanged. Mathlib verdict: no match for algebraic spaces; the returned affine-cover declarations are for schemes.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-etale-scheme-map-open-image.json`: one new statement-only supporting theorem, Tag 06NF. Mathlib verdict: no match. Searches returned scheme etaleness, scheme open immersions and their ranges, rather than an algebraic-space open-image factorization.
- `citations.json`: eleven entries, one per cited node per step, with verbatim statement quotations.

No unit/chapter file or Lean file was written. The sandbox started empty; the current item was copied before editing. Its existing searches and blueprint ancestry are retained. `searches.jsonl` records the additional searches, and their actual results have been read. `write_split.py` is the sandbox-local editing helper, not part of the DAG delivery.

## 2. Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, `AlgebraicSpace`, algebraic-space spelling variants, and affine-atlas phrases found no project declaration stating this item or the new open-image theorem. No source declaration is being treated as a finished proof.

## 3. Wanted literature

None. All sources used are present locally.

## 4. What needed repair

The item had no proof. Its source, Stacks Tag 03FY, invokes the affine-piece atlas construction 03FX and the open-image theorem 06NF. I expanded the former inside the proof, using the existing affine-basis and etale-composition Mathlib leaves, and made only the latter a new node. There is no statement dispute or source error. I did not infer that an algebraic space itself has an affine Zariski cover, or that the images of affine charts are schemes. The images are open algebraic subspaces with affine etale atlases.

The source's final sentence leaves factorization through the affine base open implicit. Step 4 gives the scheme-test argument, including field-extension lifts and the unique restricted scheme map. This avoids citing a definition for a descent theorem or assuming an unrecorded general topological factorization theorem for algebraic spaces.

The inherited chapter/unit and blueprint ancestry are preserved. I read the recorded Rankin unit and the current main-20261015 ancestor support proof. This item's geometric role is the existing auxiliary 03XX schemehood input, through `lem-a1-separated-locally-qf-space-representable` and `lem-a1-separated-etale-space-scheme`; it does not replace the Rankin argument. All reused proof tools are definitions or Mathlib leaves, and the new theorem inherits the item's unit.

## 5. Unfinished work

The new general open-image theorem is intentionally unsplit. Its proof, proof dependencies and proof origin are empty, as required for one-level splitting. No part of the item's argument is postponed to a renamed copy of its conclusion.

## Not duplicates

`lem-a1-etale-scheme-map-open-image` vs `lem-a1-etale-quasi-affine-image-scheme`: the existing theorem assumes a separated locally quasi-finite space over an affine scheme, an affine etale base change, and a representable quasi-affine open in that base change, and concludes that its image is a quasi-compact *scheme*. The new theorem allows an arbitrary algebraic space and arbitrary representable etale scheme map; its image is an open *algebraic space*, with no schemehood or quasi-compactness conclusion. The existing theorem cannot supply the general 06NF factorization.

No existing node has Tag 06NF or the label `lemma-etale-image-open`. Whole-DAG keyword searches and `blueprint_refs.py search` for `06NF`, `03FX`, `etale image`, `open image`, `affine atlas`, `affine open covering`, and `surjective etale` found no duplicate statement. The hits on affine covers and finite trivializations require extra hypotheses or concern schemes. The item's `same_as` and the new node's `same_as` are consequently empty.

## Review by N5

I read Stacks `spaces-properties.tex`, Tag 03FY (`lemma-union-of-quasi-compact`, lines 725-745), its cited 03FX construction (lines 700-722), and 06NF (`lemma-etale-image-open`, lines 535-558). The new node states precisely the first open-image/factorization part of 06NF; it does not import its unneeded quotient-presentation conclusion. I also read 03BZ and 03IE for context, without using them as uncited black boxes. The proof below replaces the final topological shorthand by a direct scheme-test calculation. For the existing elementary geometry inputs I read Schemes 01IT (`lemma-basis-affine-opens`, lines 1951-1960) and Morphisms 02GN and 02GP (`lemma-composition-etale`, `lemma-open-immersion-etale`). I opened every cited DAG node and checked its statement against the exact uses, rather than reading its proof as an interface.

Step 1 uses the atlas-existence sentence of `def-trf-algebraic-space`, `lem-weil-pbc-affine-opens-basis` on S and then on the inverse-image open in V, and the universe bound in `def-weil-size-convention`. These nodes actually supply the scheme atlas, affine neighbourhoods inside a prescribed open, and a set-sized index. Every v maps into the chosen affine base open; the source is a scheme, so restricting the scheme map gives the required factorization. No quasi-compactness of V or S is needed.

Step 2 uses the scheme-test representability/etaleness clauses of `def-trf-algebraic-space`, the explicit open-subscheme description of `def-weil-open-immersion`, and clauses (1) and (2) of `lem-weil-pbc-etale-composition-cancellation`. For every T to X, P is a scheme by atlas representability; its projection to T is etale by the atlas hypothesis. Taking the inverse-image open of U_i represents the smaller fibre product, so both morphisms in the cited composition lemma are scheme morphisms, and its etaleness hypotheses hold. No uncited theorem about composition of algebraic-space maps is assumed.

Step 3 applies the new 06NF node to the exact representable etale scheme map just checked. Its statement gives all three properties of U_i to X_i and the equality of the image point sets. Coverage then uses the scheme-test definition of surjectivity from `def-trf-algebraic-space`: the atlas pulled back to Spec K is a nonempty scheme. A point of it supplies a residue extension L and a map to V, which factors through an affine open U_i containing its point by the open-subscheme description in `def-weil-open-immersion`. Thus its composite and the original map to X represent the same field-valued class. No rational-point lift over K itself is assumed.

Step 4 uses only the scheme-test surjectivity clause of `def-trf-algebraic-space` and the restriction description of an open immersion in `def-weil-open-immersion`, together with the maps constructed in previous steps. It is marked elementary because it explicitly applies the definitions: over each residue field of each T to X_i a nonempty fibre gives an extension lift to U_i. Extension of a field does not change the image point in S, so every point of T lands in W_i. Restricting the map and its sheaf map gives the unique T to W_i. Uniqueness makes these restricted maps natural in the scheme test, which is exactly the morphism X_i to h_W_i. No sheaf-epimorphism or effective-descent theorem is concealed in this step.

I checked delivery-errors B through E against the actual files. The single new node introduces all objects and uses inline point-class and open-subspace definitions with their definition nodes; it has no proof sketch. Its source has the verified tag and TeX label, and JSON contains ordinary single TeX backslashes after decoding. The searches were actually run with msearch and have exact tool/query records. Both semantic phrasings for the new theorem return only scheme statements, while the name/pattern and whole-Mathlib grep give no algebraic-space match. Existing scheme lemmas are reused as leaves instead of recreated. The new theorem is a general local-image tool, not the item's affine covering conclusion. Every non-elementary step has the cited theorem it needs, and the proof-dependency list is exactly the union of the uses. `citations.json` takes verbatim sentences from those statements. All four proof steps are below 900 characters, so no step exceeds the long-step review threshold.

The small cases are consistent: for empty X choose the empty atlas and empty index set; if S is empty every S-scheme test is empty as well; for an empty U the new theorem has empty open image, and the map to that image is still etale and surjective on scheme tests. For a scheme X the construction reduces to ordinary open images of etale maps, but never claims those images affine. Non-quasi-separated and non-quasi-compact spaces cause no extra hypothesis: all affine choices are local, all index sets are sets in the size convention, and no intersection of affines is assumed affine. I corrected the initially considered redundant affine-disjoint-union supporting node into direct steps using the existing leaves; only the genuinely non-elementary 06NF input remains new.
