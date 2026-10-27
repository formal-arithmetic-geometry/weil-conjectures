# Worker report

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-residue-algebra-finite-type-model.json` (statement, split; no exact whole-item Mathlib match), `citations.json`, and this report. New nodes: 0. New Mathlib leaves: 0. The existing leaf `lem-weil-common-extension-fields-quotient-field` is reused.
2. Attachments: none. Searches of the live project under `lean/WeilConjectures/` by blueprint id, residue algebra, and generating-family/quotient terminology found no declaration stating all clauses of the item. Abstract quotient finite type and finite module basis theorems cover fewer clauses or require extra hypotheses.
3. WANTED: none.
4. The statement is unchanged and true, including zero quotient algebras. The source locator inaccurately attributed the general residue-field discussion to fields.tex section-examples; it is in Tag 09FB, section-introduction. Corrected only that locator. The imported node had no proof. Its older Mathlib searches remain intact; the searches performed for this split are appended and logged in searches.jsonl. No original report or split existed in this sandbox.
5. Unfinished mathematics: none. No Lean was written or compiled, no repository or launcher file changed, and no git command run directly.

## Sources and route

Read GOAL.md, the three levels in SETUP.md, the stage-1 brief and stage document, worker role, chapter sec-trace-formula and unit sk-i-curve-zero. Read the current blueprint proof of lem-trf-local-term-locality, including its specialization route; this auxiliary commutative algebra statement belongs to its previously split Tag 0GSG branch as specified by the existing blueprint.from record. Nothing in the unit or chapter is changed.

For this item, read Stacks algebra.tex Tag 00F3 (definition-finite-type), clause (1), Tag 00FM (section-Noetherian), its opening definition, Tags 00AQ and 00AR (section-conventions and section-rings-basic), and fields.tex Tag 09FB (section-introduction), which recalls both the two ideals of a field and local residue fields. The explicit quotient representative and finite polynomial sum calculations are supplied by Q88 and marked agent-written. No SGA source is used.

## Searches and reuse

Whole-DAG searches by quotient-field, field/Noetherian, and quotient-algebra terminology found the existing quotient-field leaf, the algebra/hom/quotient definition, the finite-type definition, the field definition and the Noetherian definition. Each cited statement was opened. Blueprint searches by residue field, quotient algebra, generating family and coefficient reduction found no equivalent full statement; same_as is empty. No new node is needed: residue-action well-definedness and polynomial compatibility are two-or-three-line representative calculations and therefore proof steps, not new lemmas.

Mathlib searches used only msearch.py, with two semantic phrasings, a valid Loogle query, a source grep and LeanSearch. All answers were read. In particular the module-basis results require finite free modules, which C is not assumed to be; algebra_finiteType_of_liesOver presupposes equality of the contraction and the base ideal, whereas C may be zero here. Algebra.FiniteType.quotient retains the old base, and the generators/aeval results do not supply the constructed quotient-base action. Opened the quotient-field and residue-field sources and Finiteness/Quotient.lean to check these distinctions. Consequently the item receives a direct split, not a whole-item Mathlib-leaf claim.

## Not duplicates

No new nodes were created. The existing maximal-ideal quotient-field lemma is cited rather than duplicated; the two elementary compatibility calculations remain in the item.

## Review by Q88

I checked the unchanged statement against 00F3 and the basic ring conventions, with 09FB for the residue-field assertion and 00FM for Noetherianity. The hypotheses impose no Noetherianity on A, no flatness, no injectivity of A to C, and no nonzero condition on C; none is used. No new statement needs a source or small-case audit.

Step 1 cites lem-weil-common-extension-fields-quotient-field, whose statement says precisely that a commutative ring modulo a maximal ideal is a field. A is commutative and its specified ideal is maximal, so its hypotheses hold. It is an existing Mathlib leaf, so using it as an algebra tool from another unit does not change the route.

Step 2 cites def-weil-field for inverses and def-weil-pbc-noetherian-ring for finite generation of ideals. It proves, rather than assumes, that every ideal is zero or the whole field: a nonzero x in the ideal gives 1 by multiplying by its inverse. These two ideals have respectively the empty generating set and the singleton 1. This is elementary and needs no new Noetherian-field lemma.

Step 3 cites def-weil-pbc-algebra-hom-quotient only for the quotient ring/map and the meaning of an algebra structure. That definition does not state descent along the base quotient, so the proof does not take descent from it: it explicitly checks independence of a representative using a-b in m and its image in mC, checks ring operations on representatives, and obtains uniqueness because every residue class is represented. This avoids a C4 overclaim of a quotient universal property that the cited statement never gives.

Step 4 uses the same quotient definition for surjectivity and the finite-type definition for polynomial generation. Its finite-sum formula follows directly from preservation of sums and products by q and the coefficient identity proved in Step 3. A chosen representative of any d then has a polynomial expression in the original chosen generators; the displayed formula produces exactly the required reduced family. No implicit tensor product or base-change identification is used. This verifies both the specified family and every polynomial-expression clause, beyond abstract finite type.

For small cases I checked n=0 (polynomials are constants and empty products equal 1), C=0 and mC=C (D=0 is still a unital k-algebra and generation is valid), A a field (m=0 and the formula is ordinary polynomial evaluation), and a nonflat quotient such as A=Z/4, C=A/(2). Nothing asserts injectivity of k to D, which would fail in the zero case. All steps are below 2000 characters, the whole proof is below 3000 characters, proof_deps is exactly the union of uses, and citations.json quotes actual verbatim substrings from the opened statements. I reviewed B1-B10, C1-C8, D1-D5 and E1-E7: there are no new nodes, hidden non-elementary facts, renamed clauses, or new cycles. The only correction made during review was the source locator described above.
