# Q26 stage-1 report: lem-trf-spectral-reduction-dimension-criterion

## Files written

- dag/nodes/sec-trace-formula/lem-trf-spectral-reduction-dimension-criterion.json: statement, now split in six steps; not a Mathlib leaf as a whole. Statement retained verbatim; the dimension definition is added to stmt_deps.
- citations.json: one verbatim statement quote for every step/node citation.
- searches.jsonl: actual searches made with the required msearch.py; the item retains its inherited searches and appends this session's searches.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. The existing nodes lem-trf-incomplete-spectral-algebra-norm, lem-trf-algebraic-spectral-norm-powers, lem-weil-independent-family-card-le-dimension and def-weil-vector-space-dimension supply the required inputs.

## Attachments

None. Searches of lean/WeilConjectures by the blueprint id, spectral reduction, orthogonal basis and reduction dimension found no declaration stating the item. General Mathlib results are cited through existing DAG leaves rather than treated as project attachments.

## Wanted literature

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Corollary 2.5.1/6, Theorem 3.2.1/2 and Proposition 3.6.2/8, for lem-trf-spectral-reduction-dimension-criterion. The inherited citation says that a predecessor read the scan online. The book is absent from this read clone; my attempted web opening failed because of the PDF size, and I do not claim to have read it. I have not downloaded or written a literature file. The new proof is explicitly marked proof_origin.by = agent.

I read the local Stacks source more-algebra.tex, Tag 0ASH, lemma-inequality-general, including its proof. Its normalization of a finite coefficient family and reduction against independent residues is the elementary model for the calculation here. Its theorem assumes multiplicative valuations on the extension field and therefore is NOT cited as proving our normed-vector-space or spectral-algebra assertion. The adaptation is written out. I also read Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean, especially lines 627–684 and the section hypotheses at 375–382 and 581: its power formula and algebra norm require no completeness. The norm formula is the one already defined by our existing spectral norm node.

## Problems found and corrections

No STATEMENT-DISPUTED issue was found. No hypotheses, conclusions or source fields were changed. The imported item had no proof; the split now proves every clause rather than citing BGR as an unexpanded black box. The strictness/value-group condition is used only to normalize an existing orthogonal basis; the converse equality argument instead normalizes finite scalar coefficient families, whose maximum is automatically a value of K. Full multiplicativity of s is never used. In particular I did not use the existing valued-extension-degree theorem, which assumes an absolute value on the extension, nor the spectral multiplicativity theorem requiring completeness.

The latest blueprint main-20261024 local-term-locality statement and proof, the chapter record, and the sk-i-curve-zero record were read. This item is in the inherited historical analytic support chain beneath that node. Its split preserves that chain and does not replace the current contracting-correspondence unit proof. blueprint.from.place remains the explicit inherited location; same_as is [] after whole-blueprint searches for orthogonal, orthonormal, spectral, reduction dimension and residue, and whole-DAG statement searches. The blueprint orthogonality hits concern finite-field additive characters, not ultrametric bases.

## Not duplicates

No nodes are created. In particular the Mathlib search hit isPowMul_spectralNorm is already represented by lem-trf-algebraic-spectral-norm-powers; I reused it. lem-trf-valued-extension-degree-bound assumes multiplicative extension valuations, which our incomplete spectral norm need not be, so I did not substitute it for the item. lem-trf-independent-family-cardinal-dimension is an arbitrary-dimensional cardinal bound; the finite-dimensional existing leaf lem-weil-independent-family-card-le-dimension suffices here.

## Review by Q26

I reread delivery-errors B–E against the actual item and every cited statement. There are no statement-only child nodes hiding a clause of the item, no duplicated norm construction, and no new search records claiming an unrun query. All cited nodes were opened. The quote in citations.json is copied from the statement, not a proof or docstring. None of the six steps exceeds 2000 characters.

Step 1 explicitly constructs the coefficient field and quotient vector space from the absolute-value and scalar-norm axioms. The ideal is proper because |1|=1, and its complement consists of invertible norm-one elements; products by a scalar of norm <1 vanish in the vector reduction. Thus there is no assumed residue-field or scalar-action theorem concealed in this step.

Step 2 uses exactly the basis-cardinality definition in def-weil-vector-space-dimension. Each original basis vector is nonzero, so its norm is positive and the value-group hypothesis supplies an invertible scalar of precisely that norm. The resulting coordinate formula identifies both unit balls and both open unit balls, so the quotient coordinates give an independent spanning family. This is an explicit calculation, not an uncited nonarchimedean orthogonalization theorem.

Step 3 uses the whole relevant clauses of lem-trf-incomplete-spectral-algebra-norm: definiteness, s(1)=1, scalar homogeneity, submultiplicativity and the strong triangle inequality. They give the ring, ideal and coefficient embedding. The statement of lem-trf-algebraic-spectral-norm-powers supplies exactly s(z^m)=s(z)^m for m>=1 for any algebraic extension. A finite extension meets that hypothesis. The equation converts a nilpotent residue into a norm <1, proving reducedness directly; neither a field structure on the reduction nor multiplicativity of s is asserted.

Step 4 again uses the inequalities and homogeneity of the existing norm node. Nonzero residue classes have lifts of norm exactly 1. Dividing a finite scalar family by a coefficient attaining its maximum leaves all coefficients integral and one coefficient equal to 1. If the sum had norm <1, its reduction would be a forbidden relation. This verifies both linear independence of lifts and the exact maximum norm formula, with no limit or completeness argument.

Step 5 applies lem-weil-independent-family-card-le-dimension to a K-independent finite family in the finite-dimensional K-space L, exactly its statement and hypotheses. The finite greedy construction is written out, including why an appended outside vector preserves independence and why the construction stops after at most [L:K] choices. The dimension definition then identifies the constructed basis size with the claimed residue dimension. In particular the reduction is proved finite-dimensional before using its finite dimension.

Step 6 uses the dimension definition to get n residue basis elements and the same independent-family bound to show their n independent lifts span L: otherwise an outside vector gives n+1 independent elements. The norm formula is precisely the calculation of Step 4. Conversely an orthonormal basis makes every nonzero norm equal to a coefficient maximum and hence a value in |K^x|; Step 2 applies with all its hypotheses verified. There is no approximation-of-lifts assertion or hidden Nakayama lemma.

I tested V=0 (empty basis and zero reduction), L=K (basis 1), coefficient families all zero, families of length one, and nilpotent exponent 1. A scaled one-dimensional norm N(ae)=r|a| has reduction dimension 0 if r is outside the value group, illustrating why Step 2 needs its hypothesis. For a totally ramified extension such as Q_p(p^(1/e))/Q_p, the reduction can have dimension 1<e; nothing in the argument forces equality or an orthonormal basis there. The same strict inequality is compatible with the purely inseparable extension F_p((t^(1/p)))/F_p((t)); Step 3 remains valid because the existing power lemma has no separability hypothesis. No argument uses completeness, discrete values, spherical completeness, or the existence of best approximations. All imported metadata is retained. The only off-unit proof nodes are the existing dimension definition and independent-family Mathlib leaves, so they are permitted generic tools, with no route replacement.

## Unfinished work

None for this split. Independent review and further splitting of existing dependencies belong to subsequent work. No Lean files were written and no compiler, Lake or build tool was run.
