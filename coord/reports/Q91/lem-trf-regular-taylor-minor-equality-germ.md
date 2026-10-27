# Stage-1 report: lem-trf-regular-taylor-minor-equality-germ

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-regular-taylor-minor-equality-germ.json`: statement, split; no exact Mathlib match. Seven proof steps; original statement and inherited metadata retained.
- `citations.json`: one verified verbatim statement quotation for each of the 15 step/node citations.
- `searches.jsonl`: five actual searches made through msearch.py, with their unmodified logged results. Existing Mathlib search records are retained in the item.
- `report.md`: this report. `write_split.py` is sandbox-only preparation, not a node or delivery file.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and the notions Taylor, Hilbert--Samuel and minorIdeal. The unrelated univariate polynomial Taylor and zeta-series declarations do not state this item. No compiler or Lake tool was used.

## Wanted literature

WANTED: Bierstone--Milman, *Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207--302, Remarks 9.1 and 9.5(2), pp.275--277, for lem-trf-regular-taylor-minor-equality-germ. Absent from literature/. I read those pages online in the journal-version PDF at https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf . The explicit algebraic and finite-value argument is marked agent-written, not attributed verbatim to ILO.

## Audit and changes

The item was unsplit and the sandbox contained no earlier node, report or searches. There is no repair note for this item. I read the worker brief, stage-1 document, all B--E return reasons (including their duplicated retired-run section), GOAL.md, the three blueprint levels in SETUP.md, and the chapter/unit records. The latest blueprint locality node now uses contracting correspondences and no longer has this historical resolution branch. The item nevertheless has a valid mathematical statement and is explicitly dispatched; its inherited ancestor/via chain is retained, and the split report records the historical discrepancy. Nothing above node level was changed.

The statement is unchanged. The proof was missing entirely. I supplied the regularity and coefficient comparison, generator independence, fibre dimension identity, and finite-value equality argument. No source-error or statement-dispute correction was needed. In particular the functions at nonclosed points are the stated full-variable Taylor functions, not the ordinary local Hilbert--Samuel functions with fewer variables.

DAG and blueprint searches: searched the whole DAG for Taylor, Fitting, 07Z8, 07ZA, rank/minor, quotient dimension and Leibniz/Taylor homomorphism notions, and ran blueprint_refs.py ancestor and whole-blueprint searches for Taylor, Hilbert and minor. Reused the existing coordinate-derivation lemma, formal transverse shift calculus, quotient-dimension Mathlib leaf, rank definition and Fitting presentation theorem. The supported-pivot and formal-stratum nodes have additional diagram/division assumptions, so are neither applicable generic tools nor replacements for this item. The extended-Hilbert upper-bound node contains this finite-value reasoning but also depends on principal-parts machinery; the present finite intersection of determinant opens proves the needed inequalities directly without invoking that stronger theorem. All hits from the five new Mathlib searches were read: matrix rank and invertible determinant facts, rectangular truncations and derivative truncations, and the etale locus are only ingredients. Truncation in the hits is often coordinatewise, so it was not silently identified with total-degree truncation.

## Not duplicates

No new nodes were created; there are no new/existing same-tag pairs to justify.

## Review by Q91

I read ILO VIII 2.3.11--2.3.13 on printed pp.93--94 (PDF pages 99--100), which supplies the historical resolution route but no Taylor-minor theorem. I read BM Remarks 9.1 on pp.275--276, where regular jet presentations give fixed-degree dimension loci, and Remark 9.5(2) on p.277, where cumulative ideals describe the equality germ. I also read Stacks more-algebra.tex, lemma-fitting-ideal (Tag 07Z8), its opening kernel-vector description, and lemma-fitting-ideal-basics (Tag 07ZA), including its base-change clause. The proof uses the explicit determinant formula for the latter compatibility, not an uncited assertion about flatness. Finally I read the spectrum and Zariski definitions (00DZ/00E1) in algebra.tex. There are no new-node sources to audit.

For Step 1 I opened the coordinate-derivation node and verified that its statement gives regular commuting derivations and comparison with any coordinate-valued power-series homomorphism, including iterates. The hypothesis is exactly the given etale chart over a field, and every tau_b has the required coordinate values. The formal-partial-derivative definition supplies the coefficient rule; constant coefficient after the nu derivatives gives nu! times the nu coefficient. Characteristic zero is used precisely for the inverses of factorials.

For Step 2 I opened the shift-calculus node. Its coefficient formula applies with W=T, original shifted variables Z, and phi(W)=W, which has zero constant coefficient. Apply it to f(Z) independent of W, with no auxiliary variables. This is the actual specialization giving f(T+Y), rather than substitution of a constant with nonzero formal order. Step 1 gives the derivative comparison. The determinant definition is the permutation formula, so applying tau to the finite sum/product proves minor compatibility; the minor-ideal definition covers oversized selections. No Jacobian, division or vertex assumptions from neighboring nodes enter.

For Step 3 I checked that all the work is elementary algebra written out: a truncated polynomial has its monomial coordinates; iterating commuting derivations gives the multivariate binomial Leibniz coefficients; dividing by factorials makes a ring homomorphism; expressing new regular generators through old generators maps these expressions to the same ideal of the truncated ring. The cited coordinate-derivation statement gives the commuting derivations used in that induction, and the formal-series definition gives coefficient convolution. This is not deferred to a new node that restates generator independence.

For Step 4 I opened the quotient-dimension leaf: it states exactly dim(V/U)+dim(U)=dim(V) for every finite-dimensional vector space. Here V has the N_t monomials and U is the evaluated column span, so all hypotheses hold. The rank definition explicitly supplies column-span dimension and largest nonzero minor, not merely row rank. The Fitting theorem states invariance for every finite module presented as a quotient of a finite free module, using arbitrary kernel rows. Our module Q_t/C_t is finite, and transposed columns generate its kernel, so expansion of determinants on their finite linear combinations identifies its kernel-row ideal with the displayed matrix ideal. The index k=N_t-r_t(a)-1 is used only when nonnegative. Full rank is treated separately, avoiding a forbidden negative index. This applies also when there are fewer columns than rows.

For Step 5 I read again the rank definition and minor-ideal definition. Their statements provide every asserted equivalence: all minor generators vanish exactly when rank is at most r_t(a), and Step 4 converts that inequality to H_b(t)>=H_a(t). No semicontinuity theorem is cited from a definition node. For Step 6 the same rank statement gives an actual nonzero maximal minor at a. Its nonvanishing set is a principal Zariski open by the affine spectrum definition and 00DZ/00E1; a finite intersection stays open. The finite-value hypothesis is used only to choose finitely many separating degrees. The shrinkage V_q may depend on q, as the item permits, and no infinite intersection is taken. For Step 7 both inclusions follow explicitly from Steps 5--6 and the chosen distinguishing degree of H_b if it differed from H_a.

I tested empty generators (I=0), a unit ideal, t=0, d=0, zero rank, full row rank, insufficient columns and oversized minors. Empty maximal minors in the rank-zero case are handled by delta_t=1. At a point outside X, H_a=0 and the same determinant construction still works. Nonclosed points are evaluated in their residue fields with d variables, so no change of residue-field transcendence degree is smuggled into the dimension calculation. Finite functions need not be pointwise comparable: requiring equality through the separating degrees is sufficient. These checks exposed no false case. Each step is under 2000 characters, and none hides a separate non-elementary assertion outside the opened cited statements.

## Unfinished work

None within stage 1. No Lean was written. The independent maintainer review remains the delivery protocol's next step after pushing.
