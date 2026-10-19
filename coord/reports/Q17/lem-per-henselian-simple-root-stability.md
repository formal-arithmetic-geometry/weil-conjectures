## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-simple-root-stability.json: item, split into seven explicit steps; not a Mathlib leaf.
- citations.json: verbatim statements for each citation in steps 1, 2 and 6.
- report.md: this report.

## New nodes

None. No new Mathlib leaves. The algebraic normalization is written into the item's proof rather than made into a new node restating the item or a clause of it.

## Attachments

None for this item. Searches of the read-only slopmaster2 WeilConjectures tree by the exact blueprint tag and by henselian/simple-root terms found no declaration stating coefficient stability. The results in Mathlib/RingTheory/Henselian.lean:94-153 provide monic residue-root lifting, not the topological conclusion. The existing DAG node lem-weil-pbc-henselian-local-root-lifting is reused for the one non-elementary implication.

## WANTED

WANTED: Bourbaki, Algèbre commutative VI, section 8, exercises 12 and 14(a), the reference cited by ILO XX 4.4 for the original Krasner argument. This reference is absent from the supplied literature. The present proof does not assert to reproduce those exercises: its valuation bounds and reciprocal-polynomial trick are agent-written and proof_origin.by is agent.

## Corrections and route

The statement is unchanged. Removed def-pc-field-extension from stmt_deps because no extension is introduced in the statement. The imported record had no proof. Its source correctly distinguishes Stacks 04GG from the topological consequence: 04GG alone is not a proof of stability. The proof now supplies the finite coefficient estimates, normalizes g(a+tX), converts the resulting nonmonic polynomial to a monic polynomial, applies the existing root-lifting criterion, and checks proximity and simplicity separately.

The chapter sec-deligne-laumon-a1 and unit sk-p-dl-a1-perverse were read. This is a lower-level commutative-algebra input along the existing ancestry from lem-per-artin-gabber-affine-curve Step 3, through the strict-completion and dense-field comparisons. It changes neither the unit route nor a target statement; it is not the unit's key node. The item retains its exact blueprint.from.place and ancestry. Whole-blueprint searches for henselian and simple root, plus whole-DAG searches for 04GG, simple-root lifting, stability and coefficient perturbations, found no blueprint node stating this item in another form. The same_as list stays empty.

Tool use: lem-weil-pbc-henselian-local-root-lifting is a generic local-ring criterion from another unit, declared in split_report.tool_uses. No statement of the curve-perverse unit replaces this algebraic input. The statement of that node, not anything in its proof, supplies precisely the monic residue-root lifting applied here.

## Mathlib searches

All six searches in this sandbox's searches.jsonl were run with the mandated msearch.py and their results read. Two different semantic phrasings found monic HenselianLocalRing.is_henselian and HenselianLocalRing.TFAE; the p-adic hensels_lemma has inappropriate rank-one complete coefficients. Loogle found the same monic lifting criterion. The initial grep on RingTheory/Henselian returned zero; the corrected RingTheory/Henselian.lean grep and direct reading of lines 94-153 confirm the signatures. No result states coefficient stability for arbitrary-rank henselian valuations, and the explicit rescaling argument is more than a one-line specialization. The imported searches are retained separately, unchanged.

## Review by Q17

I read ILO XX 4.4 at printed page 374: it reduces the relevant assertion to dense embeddings of henselian valued fields and cites forms of Krasner's lemma, with Bourbaki VI section 8 exercises 12 and 14(a). It does not give the perturbation proof. I therefore marked the present proof agent-written. For the algebraic input I read Stacks algebra.tex Definition 04GF (definition-henselian) and Lemma 04GG (lemma-characterize-henselian), including the distinction between its monic and arbitrary-polynomial clauses. There are no new nodes whose sources need separate review.

I checked every citation against its node's actual statement. Step 1 uses def-trf-valuation-ring only for the fraction-field characterization, which it explicitly states, and def-weil-pbc-henselian-terminology for the local maximal-ideal henselian condition. It does not infer a lifting theorem from that definition. The subring, ideal, and unit assertions are proved directly by the valuation inequalities. Step 2 uses def-weil-polynomial-ring for polynomial coefficients, degree, and evaluation and expands by the binomial formula; its derivative identity is a direct coefficient computation. Step 6 uses exactly implication (i) to (ii) of lem-weil-pbc-henselian-local-root-lifting, whose statement explicitly compares finite-algebra idempotent henselianity with monic simple residue-root lifting. The hypotheses are a local ring, henselianity in the named definition, monicity, a residue root, and nonvanishing residue derivative. Steps 1 and 5 establish these for R, Q and -1 before the invocation. citations.json copies the cited statements verbatim.

I checked the uncited steps for hidden non-elementary assertions. Step 3 writes every coefficient difference as a finite linear combination and uses its displayed valuation bound, so no continuity or implicit-function theorem is invoked. Step 4 calculates each normalized coefficient and its residue. Step 5 writes an actual polynomial formula, rather than treating a rational expression as a polynomial, and checks its leading coefficient and residue derivative. The reverse substitution and nonzero derivative in steps 6 and 7 follow by the displayed identities, not a nonmonic Hensel theorem. These are finite expansions and ordered-group inequalities, so no extra nodes are needed. Each step is under 2000 characters and the only non-elementary step names the existing lifting criterion.

For small and boundary cases I checked n=1, a=0, vanishing higher Taylor coefficients, g=f, and a zero displacement z=0. The convention v(0)=infinity makes all strict estimates valid. In residue characteristic two the residue root -1 is still a unit and Qbar'(-1)=(-1)^(n-1) is nonzero. The construction chooses a value beyond a finite set of bounds, never a large power of a fixed element; it works for higher-rank ordered groups. If the ambient ordered group has a bound beyond every nonzero field value, a zero ball is open and the topology is discrete; step 1 handles that case by a singleton coefficient neighbourhood. Thus even the possible ambient-value-group convention does not introduce a cofinality assumption.

Against delivery-errors B-E: no statement-only child has an embedded proof, no new duplicate or elementary node was created, TeX is singly escaped in JSON, and the reused criterion's source is identified by Stacks tag and label. No Mathlib hit was called absent without reading its signature. Each cited statement says exactly what is used, and every remaining fact is proved by explicit elementary calculations. The proof carries the argument itself, without moving it into a child or using a source reference as a proof. There is no completeness, rank-one, monicity-of-h, or residue-characteristic hypothesis silently added. The only issue corrected during review was the need to make h monic before using the existing monic lifting criterion; the polynomial Q resolves it explicitly.

## Unfinished

Nothing mathematical remains in this one-level split. No Lean was written or compiled. Delivery validation is recorded by the required dry run and push.
