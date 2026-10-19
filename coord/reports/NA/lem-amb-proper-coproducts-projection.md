## Files written

- dag/nodes/sec-smooth-purity/lem-amb-proper-coproducts-projection.json: statement, split by specialization of the existing reviewed torsion-ring theorem; no Mathlib match.
- citations.json: a verbatim statement quote for each citation in each of the three proof steps.

No new nodes and no Mathlib leaves. No Lean written or compiled.

## Attachments

None. The tag search in WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula.lean finds AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite at line 260, whose body is sorry. Its finite coefficient hypothesis and whole-unbounded-category conclusion agree with the repaired item, but it is not an attachment. The dualizable-object theorem earlier in the same file restricts the base tensor factor and does not prove this item.

## Wanted

None. Stacks etale-cohomology.tex and the imported master blueprint are locally available. There is no matching slopmaster2 blueprint file in the archived directory; the relevant slopmaster2 Lean docstring was read instead.

## Statement disputed and corrected

STATEMENT-DISPUTED: The imported statement has a free coefficient symbol A and does not specify its site. This is an explicit type failure rather than a claimed counterexample for some particular coefficient ring: def-weil-pbc-derived-categories defines D(T_Et,A), whereas the cited def-weil-derived-tensor now defines tensor only on D(T_proet,A), and def-weil-pbc-projection-formula-map defines a map for completed coefficient sheaves on the pro-etale site. These are different categories; substituting the etale K into those tensor/map definitions is not typed. Neither definition supplies the imported etale formula.

The correction quantifies a finite commutative coefficient ring A and fixes the unbounded small-etale categories. This faithfully exposes the intended finite stage: the unit sk-prop-sf-cbc explicitly works at A_{E,n}, the purity conventions fix A=A_{E,n}, and the slopmaster2 declaration tagged with this exact item assumes [Finite Λ]. It does not silently assert the same conclusion for discrete non-torsion O_E/E coefficients or for completed pro-etale module categories. No bound, constructibility, finite Tor amplitude or invertibility-on-the-base hypothesis was introduced. Proper finite type and Noetherian hypotheses were retained. The two tensor-order symmetries defining the canonical map are displayed, so the particular map, not just its objects, is identified.

I read the statements of every direct citer. lem-weil-delta-proper-pushforward already says finite coefficients; the other ambient nodes leave A implicit in the same finite-stage conventions. This delivery edits none of those citers and does not certify their own missing coefficient typings. In particular the repaired item cannot be used for arbitrary discrete non-torsion rings.

## Proof repair and reuse

The original geometric-stalk reduction cited only a definition of a pro-etale map, not proper base change. Its conservativity node concerns sheaves rather than unbounded complexes; the original sentence on generation of D(A) supplied no generation theorem. Instead of duplicating these repairs, I opened the already reviewed lem-kun-0f0g. It gives exactly the canonical projection map for arbitrary unbounded small-etale complexes over any torsion ring, with a fiber proof through proper base change, constant-coefficient cohomology and geometric-stalk conservativity. The finite-ring specialization and tensor-order change are written here, not made into new nodes.

The source is Stacks Tag 0F0G, etale-cohomology-lemma-projection-formula-proper-mod-n. I read the lemma and its proof in literature/stacks-project/etale-cohomology.tex, as well as the adjacent constant-complex lemma. This source expressly allows E in D(X_Et,Λ), K in D(Y_Et,Λ) and a torsion ring, without boundedness. Its geometric-fiber argument is the imported node's route. Using the more general existing theorem is a generic tool citation, declared in split_report.tool_uses, and changes no chapter or unit route. The unit has no proof steps to realize and this item is not its key statement.

## Searches and duplicates

I searched the whole DAG for projection-formula, localizing-generation and tensor/stalk notions and ran tools/blueprint_refs.py search with 'projection formula', 'proper projection' and '0F0G'. The general theorem lem-kun-0f0g and its map/tensor definitions already exist and were reused. It is a strict generalization (all proper schemes and torsion rings) rather than an equal statement under reordered notation, so blueprint.same_as is []. Imported blueprint.is and from=null are retained; there is no unspecified created-node place.

All Mathlib searches were run through msearch.py for this item and recorded in searches.jsonl and mathlib_searches. LeanFinder was tried with two distinct phrasings. The first returned light-condensed internal projectivity, adic completion and Kahler differentials; the second returned composition/transport of underived module pushforwards. None gives a projection formula for proper etale derived pushforward. Loogle returned no match for '"projection", "IsIso"'. Grep found no projectionFormula/projection_formula declarations, and the broader grep found only Witt-vector and manifold comments. LeanSearch returned Internal Server Error and is recorded unavailable. No match was inferred from an unavailable service.

## Unfinished work

None for this one-level split. Existing cited nodes remain responsible for their own downstream proofs. This is not a claim that the sorried Lean theorem or the entire dependency closure has been proved. Delivery is left to the second reader.

## Review by NA

I read the master node and its complete proof, the chapter and unit records, the finite-stage conventions and the tagged slopmaster2 theorem. Against Stacks 0F0G, I checked the coefficient category and all objects: L is on V_Et, K is on T_Et, tensor is over the constant A-sheaf, and r-star denotes exact inverse image rather than completed pro-etale pullback. The only coefficient assertion used is finite implies torsion, proved in step 1. This resolves the unbound A and the mismatched tensor/map dependencies.

For step 1 I opened prop-weil-pbc-inverse-image-modules-exact. Clauses (1)-(3) give the constant-ring identification, equality with module pullback, exactness and the module adjunction. Exactness makes termwise inverse image preserve cohomology and hence quasi-isomorphisms; this deduction and the repeated-multiples argument are elementary and written out. I did not take exactness from a definition of inverse image.

For step 2 I opened the full statement of lem-kun-0f0g: it asserts that the canonical PF_f(E,K) is invertible for a proper f, torsion Λ, and arbitrary unbounded E,K. Substituting r,A,L,K checks each hypothesis directly. The theorem does not assume schemes finite type over a field, a finite-dimensional base, or bounded complexes. I also read its reviewed fiber proof to check that reuse is consistent with the imported route, without borrowing objects from that proof. Step 2 cites its statement only.

For step 3 I opened def-kun-derived-tensor and def-kun-projection-formula-map. The former writes the total differential and the sign symmetry; the latter writes the exact adjoint-of-counit map with the factors reversed relative to this item. The two displayed swaps therefore identify the ordered map precisely. Swapping twice gives sign 1, and functoriality sends the explicit inverse swap to an inverse after Rr_*. No uncited cohomological or generation result is hidden in this step.

The small cases are the zero coefficient ring, empty V, identity r, zero K or L, and arbitrary shifted complexes. The zero ring satisfies n1=0 with n=1; the zero tensors give the zero-object identity in the empty/zero cases; the identity map gives the tensor identity after the two swaps; the (-1)^{pq} formula checks the shifted cases and arbitrary unbounded total tensors. These require no nonzero-ring or boundedness hypothesis. Since there are no new nodes, no elementary fact or restated clause was promoted to a new lemma. The citations are copied verbatim and each proof dependency is exactly a step's uses entry. I checked delivery-errors B-E: standalone typing, source tags, actual recorded searches, correct citation statements, no borrowed proof constructions, no duplicate children, no shifted coefficient category, and no added invertibility or Tor hypothesis. All substantive corrections are stated above.

## Second reading by NA

- Item statement: checked each hypothesis and coefficient category against Stacks 0F0G (`etale-cohomology.tex`, `lemma-projection-formula-proper-mod-n`), the imported item, `sk-prop-sf-cbc`, and `def-pur-conventions`; PASS for the explicitly reported finite-coefficient/site repair. Properness, finite type and Noetherian hypotheses are retained; all complexes are unbounded small-etale complexes, and no invertibility or Tor restriction is introduced. The tagged slopmaster2 theorem at ProjectionFormula.lean:260 has `sorry`, so supplies intended typing but no finished proof. The exact master checkout contains no corresponding etale ProjectionFormula.lean, and is not used as evidence of a proof.
- Step 1: checked `prop-weil-pbc-inverse-image-modules-exact` clauses (1)-(3); PASS. Finite implies a positive integer kills the ring, and exact termwise inverse image preserves cohomology and quasi-isomorphisms. No derived projection theorem is hidden here.
- Step 2: checked the complete statement of reviewed `lem-kun-0f0g` against Stacks 0F0G; PASS. Proper r and torsion A suffice for precisely the canonical map at arbitrary L and K. Only that statement is used, not its proof's constructions. Existing generic tool reuse replaces the imported proof's uncited stalk/base-change and generation assertions without creating a restatement child.
- Step 3: checked `def-kun-derived-tensor`, `def-kun-projection-formula-map`, reviewed `lem-kun-tensor-sym`, and Stacks 06YU (`sites-cohomology.tex`, `definition-derived-tor`, following paragraph); REPAIRED. A signed chain swap alone did not justify its descent through K-flat models. The step now cites the existing derived symmetry theorem, identifies both applications, writes the functorial inverse equations, and gives the composite inverse. Marked non-elementary because derived symmetry is a theorem input.
- New nodes: none; PASS B1-B7 and C5/D1-D2 vacuously. Existing `lem-kun-0f0g` is strictly more general, and `lem-kun-tensor-sym` gives the missing tensor-order tool. No elementary fact or item clause was made into a node.
- Edge cases: checked zero ring (the killing integer can be 1), empty V, identity r, zero L or K, and shifted/unbounded complexes; PASS. Derived symmetry and its inverse apply without boundedness or nonzero-ring assumptions. The identity case cancels the two factor swaps; empty/zero cases give maps between zero objects.
- Citation audit: opened all five proof dependencies and all statement dependencies; PASS after regenerating verbatim quotes for the repaired step. Sources use the appropriate tag/label; the statement's source remains the imported blueprint. No live node or Lean file was edited. The unit has no proof steps and this item is not its key statement. Additional cross-unit symmetry use is proposed in split_report only, for maintainer authorization, not installed in top-level tool_uses.
- Independent searches: ran msearch grep `projectionMap|projectionIso|projectionFormula` on CategoryTheory (0 hits) and LeanFinder with a right-adjoint/monoidal-pullback phrasing (8 underived module pullback/adjunction hits); PASS, no matching proper derived projection formula. Actual results are in searches.jsonl and the item search records. No new Mathlib leaf is claimed.

Changes: reused `lem-kun-tensor-sym` in statement and proof dependencies; replaced step 3's unsupported derived descent with that theorem and explicit inverse composition; updated citations and recorded independent searches. The first worker's finite-coefficient dispute and correct steps 1-2 are preserved. No new nodes, no Mathlib leaves.
