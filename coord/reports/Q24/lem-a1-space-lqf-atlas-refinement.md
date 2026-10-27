# Stage-1 report: lem-a1-space-lqf-atlas-refinement

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-space-lqf-atlas-refinement.json: item, statement; split into five steps; no Mathlib match.
- citations.json: one verbatim statement excerpt for each use in each proof step.
- report.md: this report. searches.jsonl is maintained by the prescribed msearch command.

New nodes: 0. New Mathlib leaves: 0. The statement and statement dependencies are unchanged.

## Attachments

None. Searching lean/WeilConjectures for the blueprint tag and for AlgebraicSpace, algebraic space and atlas found no declaration stating this item. The returned atlas declarations concern vector bundles and universal thickenings, not algebraic-space charts. No finished attachment was inferred from sorry declarations.

## Wanted literature

None.

## Problems found and corrected

The live item had no proof. Its entire conclusion is now justified rather than replaced by clause-sized child nodes. I reused lem-a1-scheme-lqf-etale-source-locality, which already states both the etale-precomposition implication and its converse for a surjective etale source map. I did not create another source-locality or common-refinement node. General reassociation of fibre products is not quoted without justification: both needed natural isomorphisms have explicit inverse maps in steps 2 and 3.

No statement dispute was found. In particular an arbitrary chart v need not be surjective: only the other map, the atlas, supplies the surjectivity of p. The projection q is asserted only to be etale. Scheme local quasi-finiteness is the finite-type convention of pqf-def-quasifinite. Mathlib's class with that name explicitly omits local finite type (Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean, lines 18-22), and none of the search hits states the algebraic-space assertion.

The blueprint ancestor lem-a1-affine-hc0 in main-20261015 has a statement but no proof of these geometric inputs. The inherited blueprint.from.place records the branch through 03XX/03XW and the old permanence steps being served. This split preserves that branch; it does not alter the unit or chapter route. The ancestor was checked with blueprint_refs.py ancestor; blueprint searches for quasi-finite, atlas and 03X4 found no imported node giving this entire atlas-refinement statement. The DAG already supplies all inputs, so there are no new-node duplicate pairs.

## Unfinished work

None in this one-level split. Existing child nodes remain their own stage-1 or later-stage items. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes were created. Existing source-locality, algebraic-space fibre products, scheme-as-space conventions, scheme fibre products and Yoneda full faithfulness are cited instead.

## Review by Q24

I read the local Stacks source spaces-morphisms.tex at Tag 0ABM (lemma-base-change-quasi-finite-locus), including its atlas diagram, and Tag 03MJ (lemma-local-source-target), including its common-refinement proof. I read the definition at Tag 03XJ. I also read descent.tex at Tag 03X4 (lemma-locally-quasi-finite-etale-local-source), spaces.tex at Tags 025Y and 025V and lemma-fibre-product-spaces (02X2), and categories.tex at lemma-yoneda (001P). There are no new nodes requiring further source reviews.

For step 1 I opened def-trf-scheme-algebraic-space: it explicitly regards the actual Yoneda sheaf of a scheme as an algebraic space, so the hypotheses F,G,H of lem-trf-space-fibre-products-etale-covers are met with X,h_B,h_T. That latter node states existence of the algebraic-space fibre product, not merely closure of schemes. I used lem-galois-yoneda-fully-faithful only for transformations between two representables, exactly the bijection it states, to obtain U -> T. I opened def-pc-fibre-product and checked that it gives existence and the complete universal property needed to form U_B without any finiteness or separatedness condition. The algebraic-space fibre-product theorem is a generic tool in another unit; split_report.tool_uses declares this use and why this unit needs it.

For step 2 the only inputs are that universal property and the explicit representable-sheaf conventions in def-trf-algebraic-space. The two section formulas are inverse on every scheme H. The equation a(u)=x eliminates x, and the remaining compatibility is exactly c u=b beta. Restriction commutes with both formulas because all components restrict by precomposition. This is a direct calculation, not an unproved representability or descent assertion.

For step 3 I again read the scheme-test sentence of def-trf-algebraic-space. For the arbitrary D -> X_B, the inverse formula inserts beta_D(d); it does not choose a lift. Its well-definedness uses f t_X=b beta_D, which follows from the given map to X_B. The test scheme E exists and E -> D is surjective etale by the stated meaning of the assumed atlas a. The isomorphism is over h_D, so the test projection for a_B is that exact map E -> D. This establishes the claimed property for every scheme test, with no independent assumption of representability of X_B -> X. Nothing here uses the proof of the cited definition or of another node.

For step 4 I checked the same definition supplies both projections separately. Testing a_B at V gives W and p surjective etale. Testing v at U_B gives the same represented fibre product with its factors exchanged and gives q etale. If different representatives are chosen, their canonical isomorphism over U_B identifies these projections. The equality of the two maps to B is obtained by projecting the defining equality in X_B. The Yoneda node explicitly states injectivity as part of its bijection, which is exactly what is needed to obtain equality of scheme morphisms. I do not use its stronger general Yoneda lemma, which is absent from that node's statement.

For step 5 I opened the statement of lem-a1-scheme-lqf-etale-source-locality and checked both applications. First its U,V,T are W,U_B,B and its p is q, whose etaleness was obtained in step 4. Then its U,V,T are W,V,B and its p is p, which is both etale and surjective. Its g p is the very same map W -> B as r q by the equality from step 4. The node explicitly allows arbitrary schemes and imposes no quasi-compactness, separatedness or Noetherian hypothesis. Thus the two implications supply precisely both conclusions of the item, in the correct finite-type sense of local quasi-finiteness.

I checked delivery-errors B through E against these uses: no statement-only child hides a proof, no elementary fact or clause has become a new node, every non-elementary input is a cited statement, and citations.json contains exact substrings of those statements. None of the five proof steps exceeds 2000 characters. The original statement and its hypotheses were retained. For edge cases I checked B empty, V empty, and U empty. If U is empty its surjectivity forces all scheme tests of X empty, and the explicit formula makes U_B and its tests empty; any chart V is then empty as well. The implications of source locality also include the empty scheme. An identity chart and an identity base change recover the ordinary common-refinement calculation. A chart v that is not surjective still gives q etale without falsely giving it surjectivity. No intersection is assumed affine and no quasi-compact atlas is chosen.

The prescribed Mathlib searches ran under this item's Q24 log: two LeanFinder phrasings, Loogle, grep in AlgebraicGeometry and LeanSearch. I read the returned scheme and cover signatures and the local QuasiFinite.lean definition. The full logged summaries were appended to the existing item searches; earlier records were retained. The verdict is no match, not unavailable, because all five commands returned successfully. The dry run and push below are the only git-producing operations, through the authorized delivery tool.
