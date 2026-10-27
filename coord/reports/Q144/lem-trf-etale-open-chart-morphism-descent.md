# Stage-1 report: lem-trf-etale-open-chart-morphism-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-open-chart-morphism-descent.json`: statement node, now split into eight steps; not a Mathlib leaf.
- `citations.json`: verbatim statement excerpts for all 23 step/node citation pairs.
- `report.md`: this report. The required search command generated `searches.jsonl` in this sandbox.

No new nodes; no Mathlib leaves. No unit file is changed: this item is a generic helper several levels below the unit's statement, not its key node.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact node id and the notions invariant opens, atlas, algebraic space, and etale/open descent. No project declaration states the item. Scheme-level fpqc descent and invariant-descent files do not supply this algebraic-space statement. No sorry declaration is counted as an attachment.

## WANTED

None: all sources used are present locally.

## Problems found and corrections

The imported statement is mathematically sound and is preserved verbatim. I checked TeX escaping in the decoded JSON and confirmed that it already uses single backslashes. Every hypothesis and conclusion is preserved, including the absence of quasi-compactness, separatedness and affine-overlap assumptions. No STATEMENT-DISPUTED finding.

The proof was empty. A tempting direct use of scheme fpqc open descent would need an extra refinement argument because the given atlas is not assumed quasi-compact. I instead use the existing `lem-trf-fppf-local-open-subfunctor-descent`, which explicitly handles an arbitrary fppf covering and gives the full scheme-test and base-change statements. Before citing it I construct the necessary subsheaf and verify the cartesian identification with the given open; these are hypotheses of that lemma, not conclusions silently assumed.

The item source cites Tag 0D2Z, whose proof says “Omitted. Hints”. I read those hints in `spaces-divisors.tex`, along with the actual invariant-open proof in `spaces.tex` 02WU and the open-subspace construction in `spaces-properties.tex` 03BZ. The hints do not prove this general morphism descent theorem verbatim. The proof is therefore honestly marked `proof_origin.by = agent`: the missing morphism gluing, test naturality, equality detection and relative-base checks are written explicitly from the sheaf equalizer axiom, rather than attributed to an unwritten Stacks argument.

The current `main-20261015` ancestor `lem-trf-local-term-locality.proof.md` and the current unit text use contracting correspondences. I read both. This item's provenance is the historical polarized-descent helper chain already recorded in `blueprint.from.via`, specifically the open/relative-Proj chart gluing required in `lem-trf-space-line-module-proj-map`, steps 2–3. This generic helper does not replace the current unit route. The existing ancestor and full via chain remain intact; the split report records this distinction.

## Searches and Mathlib verdict

The inherited search records are retained. I ran five fresh logged searches with the prescribed `msearch.py`: two different LeanFinder phrasings, Loogle, grep in `AlgebraicGeometry`, and LeanSearch. All services answered successfully. The exact queries and actual hit names are recorded in the item and the sandbox log. No unavailable service is reported as absence.

The first LeanFinder response gives scheme/locally ringed space open-immersion uniqueness and scheme etale notions, not algebraic-space descent. LeanSearch and grep find `AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`; I read `Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`, especially lines 131–145. It descends a property of a supplied scheme morphism and requires the fpqc hypotheses, rather than constructing this open algebraic subspace and its morphism. The second LeanFinder response gives `Scheme.LocalRepresentability` Zariski gluing constructions; I read `Mathlib/AlgebraicGeometry/Sites/Representability.lean`, lines 45–150. They glue schemes from relatively representable open charts and do not state etale-atlas descent for arbitrary algebraic spaces. Loogle returns no hits. None is an exact or one-line specialization matching all the item clauses.

## Not duplicates

No new nodes were created, so there are no new/existing pairs sharing a tag. I searched the whole DAG for 02WU, 03BZ, 0D2Z, invariant opens, and open descent, and searched the whole imported blueprint with `blueprint_refs.py` for `invariant open`, `descent open`, and `compatible morphisms`. No blueprint statement states this item in another form; `same_as` stays empty.

`lem-trf-fppf-local-open-subfunctor-descent` is reused as the geometric descent tool. It assumes a subsheaf with a specified cartesian chart and proves open representability; it does not construct that subsheaf from an invariant open or descend a map to Z. `lem-trf-etale-relation-finding-opens` concerns a restricted quotient, not compatible morphisms. `lem-a1-space-etale-open-image` and its scheme-map specialization concern image opens and introduce point-topology facts unnecessary here. `lem-trf-invariant-open-image-pullback` assumes a quasi-compact scheme cover. Thus no existing result is duplicated and no extra helper node is needed.

## Review by Q144

I checked B–E of `coord/delivery-errors.md` against the statement, each proof step, and the cited node statements. For the item I read Stacks 02WU (`spaces.tex`, lemma-finding-opens), 03BZ (`spaces-properties.tex`, lemma-open-subspaces), 0D2Z (`spaces-divisors.tex`, lemma-invertible-map-into-relative-proj), 00VM (`sites.tex`, definition-sheaf-sets), the fppf covering definition in 021L (`topologies.tex`), and 025Y (definition-algebraic-space). I also checked 02WY (lemma-representable-over-space), which supports the automatic-algebraic-space assertion explicitly present in the open-subspace definition node. There are no new nodes requiring additional source review.

Step 1 uses exactly the scheme-test representability, surjectivity and etaleness stated in `def-trf-algebraic-space`, the flat/locally-finite-presentation clauses of `def-weil-etale-morphism`, and the covering criterion in `def-pc-fppf-site`. Hence the single cover E_a→B is fppf without quasi-compactness. This is an application of definitions, not an unproved fpqc-refinement theorem.

Step 2 uses the sheaf clause for X in `def-trf-algebraic-space`, and the covering composition, pullback and sheaf equalizer axioms explicitly stated in `def-weil-pbc-sites-and-cohomology`. Local lifts persist under pullback and can be composed with covers witnessing membership. This proves G is a subsheaf directly; no sheafification or image theorem is hidden here.

Step 3 uses `def-trf-algebraic-space` for representable test functors, `def-trf-scheme-algebraic-space` for the actual fppf sheaves h_O and h_V, `def-weil-open-immersion` for an inclusion into an open subscheme, and the equalizer axiom again. The pair (v_i,w_i) is a section of the specified kernel pair R, and invariance forces the first projection into O whenever the second is in O. The resulting local maps glue because the open inclusion is injective on maps. Thus the identification required by the next step has been proved on all tests, naturally.

Step 4 cites `lem-trf-fppf-local-open-subfunctor-descent`. I opened its statement and checked every hypothesis: F and G are sheaves; G→F is sectionwise injective; local lifts are from step 1; and h_O=h_V×_XG is step 3. Its conclusion states exactly open representability, the unique B_O, independence of covers, and compatibility with arbitrary test base changes. `def-a1-space-open-subspace` explicitly states that such a subfunctor is automatically an algebraic space. There is no appeal to a fact merely in either cited node's proof.

Step 5 verifies uniqueness of the open as equality of subfunctors, using the sheaf clause of `def-trf-algebraic-space` and `def-a1-space-open-subspace` for U'. Both inclusions of section sets are proved by local lifts and gluing; uniqueness is not inferred just from point images.

Step 6 uses only the fppf-sheaf definition for Z and the existing compatible-map hypothesis. Its overlap is E_a×_BE_a, not a product over S. The two maps to V determine a map to R_O, so the displayed compatibility on q is precisely the equalizer relation. This glues an actual section of Z(B), without any representability assumption on Z's atlas or any choice of affine overlap.

Step 7 uses `def-pc-fibre-product` for the base-change identification of E_a under a test map, and the sheaf and natural-transformation clauses of `def-trf-algebraic-space` and `def-weil-pbc-sites-and-cohomology`. It compares the two proposed sections on the same pulled-back cover and invokes injectivity of the equalizer. For r composed with the atlas, it compares (v∘e_a,w_a) on R_O. This explicitly proves naturality and the claimed equality with q, rather than saying that the construction “transports”.

Step 8 repeats just the injective equalizer argument for arbitrary target Z'. It proves equality detection, uniqueness, and the relative-base assertion. For the last clause, `def-trf-scheme-algebraic-space` supplies the algebraic space h_T, so comparison with the structural map has the correct target. Every cited node says the part taken from it; all excerpts in `citations.json` are literal parts of those statements.

The steps other than step 4 are applications of definitions and the sheaf equalizer, each written out in a few sentences. The genuinely geometric descent theorem is a cited existing node, not classified as elementary. No newly created node restates a conclusion of the item. All steps are below 2000 characters; no long step hides a standard comparison lemma. No off-unit statement tool is used: the geometric descent node is in this same unit, and all other proof dependencies are definition nodes.

I tested O=∅, O=V, p the identity, B=∅, and Z empty. With O=∅ the local-lift subsheaf is the empty open algebraic space (its section set on the empty test is the unique section required by the sheaf axiom), and the construction gives its unique map to Z. O=V gives U=X and the usual sheaf descent of an atlas-compatible map. With p the identity, invariance is tautological and U=h_O with r=q. For an empty test, gluing has the unique section and remains natural. If Z is empty, a map q can exist only when O is empty, so no nonexistent section is manufactured. The cover is never assumed quasi-compact; R and all double overlaps may be non-affine or non-quasi-separated.

## What remains unfinished

No part of the requested split remains open. The existing geometric descent lemma remains a separate DAG task, as allowed for a one-level split; its statement, not its proof, is the only non-elementary input used here. No Lean was written or compiled and no repository or launcher file was changed. The preliminary server `review_split` passed with zero new nodes. The first full delivery dry run also passed; the final dry run checks this completed report before push.
