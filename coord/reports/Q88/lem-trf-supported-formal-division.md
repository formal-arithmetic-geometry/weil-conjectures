# Q88: lem-trf-supported-formal-division

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-supported-formal-division.json`: statement unchanged; nine explicit coefficient-recursion proof steps, status split. Mathlib verdict: no matching arbitrary finite multivariate supported-division theorem.
- `citations.json`: one verbatim statement quotation for each of the six step/node citation pairs.
- `searches.jsonl`: six actual Q88 searches, whose hits were read; their exact query texts and outcomes are appended to the item without deleting Q76's inherited records.
- `report.md`: this report and self-review.

New nodes: 0. New Mathlib leaves: 0. The field and multivariate-series definitions already supply every algebraic fact used; finite sums and the explicitly written induction require no separate lemma node.

## Attachments

None. Searched the project under `lean/WeilConjectures/` for the blueprint tag, supported-division phrases and formal-division phrases. No declaration of this item was found. Mathlib's Weierstrass and polynomial division declarations do not state it either.

## Literature wanted

WANTED: Bierstone--Milman, *Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207--302, Theorem 3.17 and Remark 3.18, printed p.238, for lem-trf-supported-formal-division. The paper is not in this read clone's literature directory. I did not claim to read its proof or invent a Stacks tag for it. The supplied proof is my own coefficient construction and `proof_origin.by` is `agent`.

## What needed repair

The item was statement-only. Its source field points to ILO VIII 2.3.11--2.3.13, which is a reference to the desingularization route rather than a proof of supported division. I read those paragraphs in the available PDF (printed pp.93--94, PDF pp.99--100): they discuss the resolution algorithm, its formal-completion compatibility and alternate algorithms. They do not establish this coefficient theorem. I kept that provenance and explicitly identified the proof as agent-written.

There is no statement dispute or hypothesis change. In particular, the divisors need not have distinct initial exponents, be monic, be arranged in increasing initial order, or form a standard basis. An empty region simply forces its quotient to vanish. The graded order is essential to the finite-predecessor argument, and it is exactly the order the item specifies.

I read the chapter and unit records and the current `main-20261015` locality proof. The item's historical via chain is still recorded, while the current locality proof uses contracting correspondences. This lower node's proof does not change a chapter or unit route or their statements. Its direct user `lem-trf-generic-monotone-diagram`, step 6, needs precisely the supported expression proved here. I do not use that user as a proof dependency.

## What remains unfinished

Nothing in this item's natural-language proof. The requested BM literature is still absent. No Lean code, compiler, Lake invocation, repository edit or launcher edit is part of this delivery.

## Searches and reuse

Before considering auxiliaries I searched the whole DAG for supported division, Hironaka, finite triangular systems, well-founded recursion and coefficient recursion, and used `tools/blueprint_refs.py search` for `formal division`, `division`, `triangular` and `well-founded`, plus `ancestor` for the item. No blueprint theorem states this arbitrary-list result. `lem-trf-jet-diagram-hilbert-control` contains a narrower vertex-family clause and several additional geometric conclusions; `lem-trf-generic-monotone-diagram` already depends on this item. Neither is used circularly. `def-trf-supported-homogeneous-division` defines homogeneous division and finite tests under additional diagram hypotheses; it does not prove the formal theorem. `lem-trf-initial-diagram-stabilization` has a finite-test conclusion for monotone diagrams and is also unnecessary for this coefficient proof.

All six fresh searches ran with the prescribed `msearch.py`. Loogle found non-zero-divisor facts. LeanSearch and the first LeanFinder phrasing found univariate Weierstrass division. I read `PowerSeries/WeierstrassPreparation.lean`, including declarations at 504, 579 and 594: their hypotheses and remainder notion are different. A second LeanFinder phrasing found `MvPowerSeries.inv.aux` and its coefficient formula; I read `MvPowerSeries/Inverse.lean:55--105`. That construction only inverts one series with an invertible constant coefficient. The Mathlib grep searches found unrelated MvPowerSeries quotient/truncation results and `MonomialOrder.div`; I read `MvPolynomial/Groebner.lean:128` and its signature. It divides polynomials by leading terms and does not give these unique formal quotients. No returned hit is an exact match or one-line specialization. All fresh services answered successfully. The exact inherited Q76 searches and their recorded results remain in the item.

## Not duplicates

No new nodes are proposed. The partition, normalized columns, scalar recursion, finite reindexing and coefficient bounds remain explicit proof steps of this item.

## Review by Q88

I checked this proof against delivery-errors B--E with the item, both cited definition statements and the available sources open. The source I actually read for the historical context is ILO VIII 2.3.11--2.3.13; I also read the current blueprint locality proof and the statements of the nearby formal/homogeneous-division nodes listed above. The BM theorem is requested above, rather than represented as a source I read. There are no new nodes whose sources need a further check.

Step 1 proves finite predecessors, existence of a least exponent and translation invariance directly from the specified degree-lexicographic order. There is no appeal to a monomial-order theorem. Step 2 proves the slot partition directly from the set differences in the item, including overlapping and equal orthants. Neither step needs an external statement.

Step 3 uses exactly what `def-weil-field` states, namely invertibility of each nonzero initial coefficient, and what `def-weil-pbc-multivariate-power-series` states, namely the finite convolution product and coefficient-family realization. Translation invariance from Step 1 then proves the diagonal coefficient is 1 and all earlier coefficients vanish. I checked that normalization scales the quotient coefficients by the inverse of the initial coefficient, even when it is not 1.

Step 4 gives the full scalar recursion, its empty-sum base case, the degree induction and the finite within-degree recursion. Every right-hand argument is strictly earlier and there are finitely many of them. No completeness theorem, infinite matrix inverse, unnamed division lemma or assumed standard-basis property is invoked. Step 5 cites the series definition for existence of the series as coefficient families and for its product formula. I checked the reindexing term by term: a supported quotient coefficient has the unique slot alpha_i+beta, and a nonzero contribution at nu forces that slot to be at most nu in the given order. The convolution sum is already finite, and adding zero terms from the finite predecessor set is legitimate. Thus the proof never forms an unjustified infinite sum of the column series.

Step 6 substitutes the recursion and uses the cited coefficient-family definition to turn equality of coefficients into equality of series. Step 7 uses that same definition for the other expression's coefficient equation and the field definition to recover each quotient coefficient from its encoded slot. Induction then proves uniqueness; no cancellation of an arbitrary sum of series is presumed. Step 8 proves the filtration bounds by induction on exactly the same order: every predecessor of an exponent below degree q is still below degree q. The quotient bound follows from |alpha_i+beta|=|alpha_i|+|beta|. Step 9 checks the empty list and the single-exponent n=0 case directly, and records why repeated initial exponents cause no uniqueness problem.

I checked small cases F=0, s=0, n=0, a constant-unit divisor, repeated initial exponents and divisors whose entire orthant was assigned earlier. The first scalar is f_0 if there is a remainder slot and is encoded in the first applicable divisor otherwise. For an initial exponent of degree d_i, a quotient coefficient of degree e is first assigned at output degree d_i+e, so no circular use of yet-unassigned quotient coefficients occurs. None of these tests requires characteristic zero or a restriction on the field. Every cited statement is quoted verbatim in citations.json; no property is borrowed from a cited node's proof. No proof step exceeds 2000 characters. All nine steps are elementary coefficient computations or ordinary induction with their formulas written out, so no non-elementary assertion has been hidden in an elementary label. I retained the statement and all original provenance and searches, and added only the split, honest proof provenance and actual new search records.
