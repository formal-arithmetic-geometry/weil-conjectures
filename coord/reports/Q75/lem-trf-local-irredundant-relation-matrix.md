## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-local-irredundant-relation-matrix.json` (statement, now split; no Mathlib match for the full item), `citations.json`, and this report. The sandbox also contains the actual search log and a preparation script. No Lean or repository file was written, and no compiler, Lake, build or git command was run by the worker.

Attachments: none. Searches for the exact blueprint tag and for irredundant/minimal generating families and relation matrices in `lean/WeilConjectures/` found no declaration stating this item. The topology declarations called irredundant concern irredundant unions of closed sets; the matrix declarations invoking a unit determinant assume or obtain it in other settings. They do not state this relation criterion.

WANTED: none.

The original statement is correct and unchanged. Its source paragraph abbreviates both the off-diagonal contradiction and the determinant calculation; the split supplies those arguments rather than treating either as an uncited black box. The source uses the same row-vector relation, so no transpose convention is changed. No work remains on this split beyond independent maintainer review.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. Three existing Mathlib leaves suffice: `lem-weil-pbc-local-ring-unit-criterion`, `def-weil-pbc-matrix-determinant`, and `lem-weil-pbc-matrix-adjugate-identity`.

## Searches and blueprint

I retained the item's five existing 2026-10-22 searches and read their reported results. On 2026-10-23 I ran the required msearch command for LeanFinder (two phrasings), Loogle, LeanSearch, and a local-ring source grep. All services returned answers. The first phrasing concerns matrices fixing irredundant tuples; the second concerns coefficients of relations on minimal families. The hits concern fixed-determinant integer matrices, Jacobian determinants of presentations, regular sequences, quotient bases, or localization. None gives the item under its hypotheses. The grep's sole hit discusses a minimal polynomial in LocalRing/Etale. Every appended query/result is copied from searches.jsonl; no unavailable search is represented as a negative answer.

I read SETUP's three levels, the chapter and unit records, and the current chapter, unit, ancestor statement and ancestor proof under literature/blueprint/latest (current commit 7284bb09daf97437d544c51882b325f9c52cd345 in COMMITS.txt). This is a small commutative-algebra input to the already recorded flattening/projective-freeness chain, not a change of the unit's contracting-correspondence route. The blueprint ancestor tool identifies lem-trf-local-term-locality. Whole-blueprint searches for irredundant, relation matrix, minimal generating, adjugate and local unit terminology found no equivalent blueprint theorem. The inherited precise from.place and via chain are preserved, same_as is [], and split_report.blueprint describes the portion realized. Whole-DAG source/key-word searches located the three reusable nodes, whose complete statements I opened.

## Not duplicates

No new nodes were created. The already existing unit criterion and adjugate identity are cited rather than duplicated. The item is not a restatement of either: it proves the local restrictions on coefficients from irredundancy and then obtains the unit determinant.

## Review by Q75

I checked the item against algebra.tex, Tag 0592, label lemma-projective-freeness-criteria, final paragraph (lines 20672–20680). It gives exactly the relations a_j = sum_i a_i b_ij and the irredundancy implication used here. I also read Tag 00E9, lemma-characterize-local-ring, statement and proof (lines 3367–3396), and the adjugate sentence of Tag 07DQ, lemma-matrix-left-inverse (2689–2691). There are no new nodes requiring further source comparisons. The determinant node explicitly gives the Leibniz formula and the n=0 convention. I read the existing Mathlib declarations at LocalRing/MaximalIdeal/Basic.lean:83 and Matrix/Adjugate.lean:264,269 to confirm the cited tools' meanings.

Step 1 uses precisely the unit/complement equivalence in lem-weil-pbc-local-ring-unit-criterion. The equation (1-b_jj)a_j = sum_{i != j} a_i b_ij follows by rearrangement. Inverting its coefficient would violate irredundancy at j. Membership of 1-b_jj in the maximal ideal and properness then imply b_jj is outside it, hence a unit. Locality is used only through the cited criterion, and maximality supplies properness.

Step 2 uses the same cited equivalence. If b_ij is a unit, solving the j-th equation for a_i gives the explicit displayed combination of the other entries. The condition i != j ensures a_j is an allowed other entry. The contradiction is irredundancy at i, not at j. No non-zero-divisor, domain, finite-generation-of-the-ring, or cancellation hypothesis is assumed.

Step 3 uses exactly the displayed Leibniz formula from def-weil-pbc-matrix-determinant and again the local unit criterion. Each nonidentity permutation supplies an off-diagonal factor in the maximal ideal. The identity term differs from 1 by an element of that ideal, by the written finite expansion of product_j(1+u_j). This proves det B-1 lies in the ideal, and properness puts det B outside it. No determinant base-change theorem, residue-field linear independence, Nakayama lemma, or unrecorded invertibility criterion is invoked.

Step 4 uses precisely the two-sided equality in lem-weil-pbc-matrix-adjugate-identity, which applies to square matrices over any commutative ring, including this R. Multiplying the adjugate by the inverse d of det B gives both inverse identities. Commutation of the scalar with the finite matrix sums is an entrywise distributivity calculation, written in the step. These are elementary steps relative to the cited statements; each is fewer than 800 characters, so none contains a long hidden comparison argument. citations.json contains every cited node at every step, with exact substrings checked against its statement.

I checked the boundary cases n=0 (vacuous coefficient claims, determinant 1, unique empty inverse) and n=1. In R=k[e]/(e^2), a_1=e is irredundant and b_11=1+e fixes it; the proof correctly gives a unit without incorrectly forcing b_11=1 or cancelling e. For a two-entry example R=F_2[x,y]/(x,y)^2 and (a_1,a_2)=(x,y), irredundancy holds and the relation forces the constant parts of B to be the identity, exactly as the argument predicts. Over a field an irredundant tuple has at most one entry, also consistent. The zero ring is excluded by the given existence of a maximal ideal, not by an added hypothesis. No statement correction or source error was needed. The corrections made to the initially empty proof are the explicit off-diagonal formula, the finite Leibniz expansion, and an actual two-sided inverse rather than the unsupported phrase 'the matrix is invertible'.
