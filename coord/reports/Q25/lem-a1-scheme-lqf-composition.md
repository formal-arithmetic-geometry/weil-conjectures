# Stage-1 report: lem-a1-scheme-lqf-composition

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-scheme-lqf-composition.json: statement, now split into four steps using existing nodes; Mathlib verdict: no exact match for the scheme-sense predicate including local finite type.
- citations.json: four entries, one for each step's cited node, copied verbatim from the statements read in the repository.
- report.md: this report. searches.jsonl was written by the authorized msearch.py commands.

New nodes: 0. New Mathlib leaves: 0. No unit record needs editing: this auxiliary item is not its unit's key statement.

## Attachments

None. Searched lean/WeilConjectures by the exact item id, by IsLocallyQuasiFinite/locally-quasi-finite composition, and by the Mathlib predicate's composition names. No project declaration states the item. Scheme.Hom.isLocallyQuasiFinite_iff, read at WeilConjectures/AlgebraicGeometry/QuasiFiniteMorphismComparison.lean:62-73, is a comparison theorem, not this composition result. Mathlib's composition instance is not an attachment of a project declaration.

## WANTED

None: all sources used are present in literature/stacks-project/.

## Problems found and corrections

The imported item was unsplit and contained no argument. Its statement is mathematically correct. I normalized doubled TeX backslashes in the statement; all hypotheses and the conclusion are unchanged. The finite-type affine-neighbourhood requirement is essential: Mathlib's LocallyQuasiFinite explicitly does not require local finite type. I did not silently substitute that predicate. Read Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean:19-24,55-87 and FiniteType.lean:68-70; the two Mathlib composition instances alone require a non-Mathlib comparison before they apply to this item. The original Q22 search records are retained, with five actual Q25 searches appended from this sandbox's log.

The inherited blueprint ancestry points to lem-a1-affine-hc0. I read the current latest blueprint statement and proof in sec-purity-real-sheaves/sk-lem-wrp-hc2/, together with the chapter and sk-p-real-rankin documents and their DAG records. The current ancestor's finite-level paragraph concerns compactly supported sections; the representability and scheme-composition branch is the inherited auxiliary implementation branch, not an extra assertion in the current blueprint text. The split stays entirely below this auxiliary node and changes neither chapter nor unit route. Searched the entire imported blueprint for quasi-finite and composition and the DAG for 01TL, 01TK, 00PO, comparison declarations and matching concepts. No imported blueprint node states this same scheme-composition assertion. The ring composition node below is an existing auxiliary node, reused rather than duplicated.

## Unfinished work

None for this stage-1 item. No Lean was written and no compiler, Lake or build command was run. The repository and launcher were read only. The prescribed delivery checks run on the server.

## Not duplicates

No new nodes. Reused lem-a1-scheme-lqf-affine-criterion for 01TK, lem-trf-quasi-finite-composition for 00PO, lem-weil-pbc-affine-opens-basis, and pqf-def-quasifinite. In particular, no new ring-composition lemma was created.

## Review by Q25

I read Stacks morphisms.tex, Tag 01TL (lemma-composition-quasi-finite), and its use of Tag 01TK (lemma-locally-quasi-finite-characterize); I read the complete 01TK statement and proof and algebra.tex Tag 00PO (lemma-quasi-finite-composition). The split expands 01TL's locally-of-type-P composition argument into pointwise compatible affine neighbourhoods. It needs only the locally quasi-finite assertion, not the separate quasi-finite/quasi-compact assertion. There are no new nodes whose sources or small cases require a separate review.

Step 1 cites lem-weil-pbc-affine-opens-basis. I opened its statement: it gives an affine neighbourhood inside every prescribed open around a point, exactly what is needed three times. First choose W around h(f(x)); continuity makes h^{-1}(W) open, then choose V around f(x) inside it; continuity makes f^{-1}(V) open, then choose U around x inside that. No quasi-separatedness is assumed and no intersection of two affines is claimed affine. This is a non-elementary invocation of the affine basis, marked accordingly.

Step 2 cites lem-a1-scheme-lqf-affine-criterion. I opened the node and checked that its implication (1) => (2) gives finite type AND quasi-finiteness at every prime for every affine pair with the image containment. Step 1 provides both required containments. Apply it to h on V,W and f on U,V. This uses the statement of that node, not its proof, and no unstated comparison between Mathlib and Stacks notions.

Step 3 cites lem-trf-quasi-finite-composition. I opened its statement: it is exactly the theorem about composable commutative-ring homomorphisms, each finite type and quasi-finite at every prime of its target. Step 2 verifies all four hypotheses for O_S(W) -> O_Y(V) -> O_X(U). The conclusion supplies finite type and the primewise property on O_X(U). I wrote the equality on sections (h o f)^#(a)=f^#(h^#(a)); this is the definition of composition of morphisms of locally ringed spaces, not an additional theorem or an unproved comparison. This ring theorem is a generic tool from another unit: split_report.tool_uses declares why it is needed, as 01TL explicitly invokes 00PO. No node of our unit supplies ring-map composition. I do not set top-level tool_uses.

Step 4 cites pqf-def-quasifinite. I opened its statement: existence of affine neighbourhoods with a finite-type map quasi-finite at the prime of x is exactly quasi-finiteness at x, and local quasi-finiteness is that assertion for every x. U,W constructed above give those witnesses. This final use of the definition is elementary and marked true. The verbatim citation includes these two clauses. No restriction-locality theorem, global finite-type theorem, or hidden quasi-compactness claim is used.

I checked delivery-errors B through E against the written proof: the statement introduces all objects and cites their notions; there are no new nodes, duplicated facts or restated clauses; the two non-elementary results and the affine basis have explicit citations; every quoted statement actually supplies what the corresponding step takes from it; the dependencies are exactly the union of uses. The existing ring theorem has no dependency on this item, and the affine criterion depends only on the lower point/affine criteria, so the chosen route introduces no cycle. The four steps are each under 500 characters, with no long inline sublemma.

For edge cases, when X is empty the pointwise conclusion is vacuous. If S is empty, existence of h and f forces Y and X empty, so no neighbourhood choice is incorrectly required. Identity morphisms, open immersions and finite maps fit the same choices. Infinite disjoint unions cause no issue: the argument works at each point and never takes a finite subcover. Non-Noetherian bases cause no issue: 01TK and 00PO impose none. These checks confirm that no finiteness, separatedness or Noetherian hypothesis slipped into the proof. The TeX normalization was the only statement edit.
