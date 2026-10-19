## Files written

dag/nodes/sec-smooth-purity/lem-pur-noetherian-algebra-module-generic-freeness.json: statement, split; not a Mathlib match. No new nodes and no new Mathlib leaves. citations.json contains the whole verbatim statement for each citation, indexed by proof step. searches.jsonl records actual search executions.

## Attachments

None. Searches of WeilConjectures in the read-only slopmaster2 and exact master sources found no declaration giving this algebra-module freeness assertion. Slopmaster2 FreeLocus.lean gives finite-base-module freeness and algebra-module generic flatness; neither proves the arbitrary-rank freeness requested here. Existing DAG attachments and Mathlib leaves are reused, not modified.

## Wanted

None: the Stacks source is present.

## Corrections and route

The item was statement-only; its statement is faithful to Tag 051R and remains unchanged. No STATEMENT-DISPUTED issue was found. The blueprint ancestor is lem-fin-generic-radicial-smoothing, proof paragraphs 2-3 (finite-presentation spreading). This algebra input belongs to the existing 052A -> 051T -> 051S -> 051R chain and does not alter the unit or chapter route. The unit is sk-prop-sf-cbc; this item is not its key node, so no unit record is written.

The Stacks proof first discusses prime filtration, then the domain case. I reordered its induction presentation: at dimension d, first prove the domain case, using only smaller dimensions, then recover all algebra-module pairs by prime filtration. This prevents the reduction to prime factors of the same dimension from appearing circular. I replaced the support-closed citation by the explicit common-denominator calculation on finitely many generators of the finite polynomial-module cokernel. The annihilator obtained lies in the polynomial ring, not necessarily in the base. Dimension drop then permits induction on its quotient algebra; it is not treated as a base scalar.

The existing lem-weil-pbc-noether-normalization-over-domain is used as a generic tool from another unit: 051R explicitly requires 07NA and the present unit has no replacement normalization theorem. Its statement, not its proof, is used. This is declared in split_report.tool_uses for maintainer review; no maintainer-owned tool_uses field is set. Field normalization is a Mathlib leaf and its dimension identification is Lean-closed.

## Not duplicates

No nodes are created. Tag 00L0 and the Mathlib name search located lem-weil-pbc-noetherian-module-prime-filtration, whose entire statement is precisely the needed theorem. Tag 07NA located lem-weil-pbc-noether-normalization-over-domain. Whole-blueprint searches for generic freeness, prime filtration, 00L0 and Noether normalization and the DAG searches were read before deciding on zero new nodes. The adjacent finite-type-algebra generic-flatness node states flatness only; the item's parent (051S) lacks the Noetherian assumption, so neither duplicates this item or supplies a usable substitute.

## Unfinished

Nothing needed for this one-level split remains. The already existing unsplit dependencies remain their own items; no Lean is written or compiled and nothing is pushed.

## Review by NK

I read literature/stacks-project/algebra.tex, Tag 051R (lemma-generic-flatness-Noetherian), including its entire induction proof; Tag 00L0 (lemma-filter-Noetherian-module), including both statements and proof; and Tag 07NA (lemma-Noether-normalization-over-a-domain), including the precise intermediate finite algebra and localization conclusion. I read the master blueprint ancestor, the chapter and unit records, the three fixed/free levels of SETUP.md, GOAL.md and coord/dag-sync.md. No new-node sources are required. I also read the closed dimension theorem in WeilConjectures/Mathlib/RingTheory/NoetherNormalization.lean:58-74 and the Mathlib prime filtration definition/theorem in RingTheory/Ideal/AssociatedPrime/Finiteness.lean:49-51,92-105. These agree with the cited DAG statements.

Step 1 uses the two localization definitions for zero fractions and inverse fractions, then proves exactness directly by multiplying a numerator by the power that kills its image. It also identifies repeated localizations; this is a calculation, not an uncited appeal to flatness. Step 2 writes out both basis localization and the section of a surjection onto a free module; no projectivity theorem or finite-rank assumption is hidden here.

Step 3 uses lem-zl-noether-normalization-field and lem-zl-noether-normalization-dimension precisely to give finiteness of generic dimension, with nonzero generic algebra checked before either is applied. It uses the prime-chain dimension definition. The zero-generic-algebra case explicitly extracts the scalar killing 1; therefore every module over the resulting zero localization vanishes.

Step 4 uses 07NA exactly as its node states: it does not assume S itself is already finite over a polynomial algebra; it uses S' and first localizes to identify S'_f with S_f. Injectivity of R -> S is obtained by separating the nontrivial-kernel case. Noetherianity of the localized base follows from contraction of ideals and finite generators, and its domain property from its inclusion in the fraction field. The dimension node applies to the injective finite generic polynomial map, identifying the number of variables with the original generic dimension. The final scalar is returned to the original base as fb, not confused with an element of its localization.

Step 5 cites the finite-module definition only for finite generators and gives the actual linear algebra: choose a maximal independent subfamily from a finite spanning family, get an injective lattice, express all generators in that basis, multiply their finitely many nonzero denominators. Hence g annihilates the whole cokernel. The same generators prove it is finite over P/(g). This is elementary linear algebra and fraction arithmetic, not another generic-freeness assertion.

Step 6 uses the dimension statement with the identity normalization of the polynomial ring; the dimension definition and explicit inverse-image/prepending of prime chains give the strict drop. The nonzero polynomial remains nonzero over the fraction field because the base is a domain. At d=0 the quotient generic algebra is zero, so the induction has a valid base.

Step 7 applies the induction only after that strict drop and uses the polynomial definition for its monomial basis. Exactness and extension-freeness were already proved in steps 1-2. Step 8 uses finite-type permanence to obtain B Noetherian and then precisely the finite B-module hypothesis of the prime-filtration node. Quotient domains have generic dimension <=d by prime chains. Every quotient is handled by the domain assertion already proved at d or a genuinely smaller induction parameter. The finite product of nonzero base scalars is nonzero, makes all quotient bases available, and the finite succession of split extensions gives the claimed basis for M.

I checked all B-E return classes against these files: no statement-only new nodes, duplicate nodes, hidden clause nodes, hollow constructions, unrun searches or missing citations are introduced; every use has a verbatim statement quote. Elementary fraction/chain/basis arguments are written in full instead of relegated to new nodes. No proof of a cited node is used as extra output. In particular the ordinary prime filtration is not replaced by an unrelated sheaf filtration. Edge cases checked are M=0, B=0, noninjective R->B, empty prime filtration, field base, no polynomial variables, unit annihilator, and infinite-rank example B=M=R[x]. The last example confirms that no finite-base-module Mathlib theorem suffices. Search hits for localization freeness were read at Localization/Free.lean:41-49,78-91 and rejected because they require finite presentation over R. LeanSearch was unavailable and is recorded as such; the successful semantic, Loogle and grep searches are retained exactly in the sandbox log.

## Second reading by NK

I reread Tag 051R (algebra-lemma-generic-flatness-Noetherian) hypothesis by hypothesis: the item has Noetherian domain base, finite-type algebra, finite algebra-module, and the exact nonzero localization/free conclusion; the zero algebra, field, zero module, n=0 polynomial ring, and infinite-rank free example are consistent. The item source and all definition dependencies were checked against their cited DAG statements; no new nodes were created, so B1-B7 are vacuous.

Step 1 was checked against the two localization definition statements and Tag 051R: the numerator-killing, lifting, and iterated-localization calculations are explicit elementary consequences. Step 2 was checked directly: common denominators prove localization of a basis, and chosen lifts of a quotient basis prove splitting; it uses no uncited projectivity claim. Step 3 was checked against the field normalization, dimension, and Krull-dimension statements: the zero generic algebra case and strong induction parameter are explicit. Step 4 was checked against 07NA, the dimension theorem, and Noetherian-ring definition; injectivity, localization, contraction of ideals, and return of the scalar are accounted for. Step 5 was checked against finite generation and the source proof: maximal independent generators, denominators, and annihilation of the cokernel are written out. Step 6 was checked by prime-chain argument and the dimension node; quotient dimension strictly drops, including d=0. Step 7 was checked against polynomial-ring, localization, and extension-basis calculations. Step 8 was checked against finite-type Noetherianity, prime filtration, and Krull dimension; the product scalar and successive split extensions are explicit. Every non-elementary citation has a verbatim entry in citations.json, and the normalization theorem is recorded as a tool use.

Changes: corrected the node's `created.item` metadata to this delivered item (it incorrectly named the neighboring finite-presentation item); added this second-reading audit required by the delivery contract. No mathematical statement or proof step was changed.
