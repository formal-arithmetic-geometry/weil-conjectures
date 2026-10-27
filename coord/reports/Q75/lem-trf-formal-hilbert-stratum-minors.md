# Q75: lem-trf-formal-hilbert-stratum-minors

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-formal-hilbert-stratum-minors.json`: statement item, split into 13 proof steps; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/node citation (full statements, to include every clause used).
- `report.md`: this report. `searches.jsonl` was written by the required search command.

No new nodes and no new Mathlib leaves. All mathematical work was done in the named sandbox; no Lean was written and no compiler was run.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for Hilbert--Samuel, equimultiple, Taylor/minors and local-flattener terminology found no project declaration stating this item. The item has Lean audit state `none`; the upstream source is not treated as a proof merely because it exists.

## Wanted literature

WANTED: Bierstone--Milman, *Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207--302, Definitions 7.9--7.13, Theorem 7.14, Lemmas 7.15 and 7.17, Remarks 9.1 and 9.5, for lem-trf-formal-hilbert-stratum-minors. The journal text is absent from the repository. I read those places online at https://www.mahalex.net/teaching/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf without adding a download to the repository. The item remains explicitly agent-origin, with the complete argument written out, because the detailed source is not a local literature document.

The available ILO volume, Expose VIII 2.3.11 and 2.3.13, printed pp.93--94 (PDF pages 99--100), was read locally. It supplies the resolution route and the reference to BM, not the claimed algebra calculation. No SGA source was used. Stacks 07Z8 (`lemma-fitting-ideal`) and 07ZA (`lemma-fitting-ideal-basics`) in `literature/stacks-project/more-algebra.tex` were read for the existing general Fitting node. No Stacks tag states the main comparison theorem.

## Statement and route audit

The original theorem's substantive assertions are retained. I made implicit conventions explicit: L is a field (rank and dimension require this), the diagram is finitely generated rather than a finite set, its vertices are distinct minimal vertices ordered by degree, the empty maximum is zero, and bounds involving d_i-1 use integer arithmetic. The finite-type clause now explicitly relates K and L to the chart and distinguished point. These clarify the objects intended by the source; no counterexample to the asserted comparison was found.

The current main-20261015 proof of `lem-trf-local-term-locality` uses contracting correspondences. Its historical alteration branch is still the recorded ancestor of this assigned item. I read that current proof and the chapter/unit records, retain the inherited provenance, and change no chapter, unit, target or other worker's node. In particular I do not claim that the local algebra here is a replacement for a contracting-correspondence step.

The imported node had no proof. The main work is now in its own steps: supported Taylor generation, the finite unit pivot, cofactor extraction, explicit block induction, and the finite-value equality-germ argument. Nothing has been moved into a new node that merely repeats the conclusion.

## Searches and reuse

I searched the entire imported blueprint with `tools/blueprint_refs.py search` for Taylor, Hilbert, equimultiple and Fitting, and obtained the ancestor with `ancestor`. I searched the DAG for those notions, the prescribed-support division terminology, and Stacks 07Z7/07Z8/07ZA. Existing Fitting independence/base change, formal differentiation, multivariate series, implicit Taylor calculus and jet-diagram dimension nodes cover the general inputs. The stabilization and coefficient-transform nodes do not state this comparison, and the latter depends on the coefficient-data branch, so neither is invoked circularly.

All five fresh Mathlib queries are recorded exactly as run by msearch.py in searches.jsonl and appended to the item, retaining the historical records. Two semantic phrasings were tried. LeanFinder returned polynomial-presentation Jacobians and a Smith-basis quotient-dimension theorem; LeanSearch returned analytic Frechet derivative and homogeneous polynomial derivative facts. Loogle and the targeted RingTheory grep returned no hits. I read the relevant `Submersive.lean` declarations (basisDeriv_apply at 624 and jacobian_eq_det_aevalDifferential at 154), `EulerIdentity.lean:48`, `FDeriv/Analytic.lean:137`, and the statement of `Ideal.finrank_quotient_eq_sum` at `LinearAlgebra/FreeModule/IdealQuotient.lean:60`. Their types do not identify derivative ideals with Taylor rank-minor ideals. No service failure was recorded as an absence result.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. Presentation independence and base change are citations of `lem-trf-fitting-ideal-independence-base-change`, rather than duplicate nodes under 07Z8 or 07ZA. The cofactor and formal inverse calculations are elementary steps with their formulas written out.

## Review by Q75

I checked the split against delivery-errors B--E with the item, its five proof-dependency statements, the ILO pages and the Stacks source open. There are no statement-only new nodes to audit. The item itself introduces its series, diagram, derivative ideal and finite matrices, with the existing minor-ideal definition added to its statement dependencies. The detailed BM locations were read online, and the local-source limitation is disclosed above.

Step 1 cites the series definition for coefficientwise finite sums and the derivative definition for its coefficient formula and Leibniz rule. Repeated application gives the displayed Taylor coefficients; no analytic convergence or analytic derivative theorem is used. Step 2 cites the actual two clauses of the Fitting independence/base-change statement, with F_t finitely generated by its N_t monomial classes and index H_t-1 nonnegative. I checked the exceptional case H_t=0 separately; a negative Fitting index is never passed to that node.

Step 3 uses the series definition and the assumed supported expansion. Its displayed coefficient sum and the downward-closure argument explain why Taylor translation preserves the allowed Y supports, including the potentially infinite sums in X. Step 4 uses homogeneous division from the item's hypotheses and coefficientwise formal inversion from the series definition. Each homogeneous basis gives a diagonal block, and the complementary monomial columns identify the selected row minor; the number of its columns is exactly r_t. There is no unproved generic freeness or flatness assertion here.

Step 5 uses the already established presentation independence, then expands a minor along a column whose entries are low derivatives. Step 6 applies a single cofactor expansion to the explicit unit pivot from step 4; factorials are units because the coefficient field has characteristic zero. Both are elementary finite determinant arguments, rather than applications of an uncited flattening theorem. Step 7 explicitly factors g as U Z and inverts U using the adjugate and a formal unit determinant. Its hypotheses are exactly the stated membership and invertible Jacobian for each accumulated block, so it needs no existence theorem for new implicit coordinates.

Steps 8--9 set up the block induction, including the empty initial block. For a derivative exponent in D of degree below the current vertex degree, the containing vertex is in an earlier block. Projecting to its essential variables gives an exponent in that restricted diagram, to which (5) really applies. The remaining derivatives use complementary variables and preserve the earlier coordinate ideal. The derivative definition supplies that elementary assertion directly on coefficients. The extraction formula treats all exponents outside D. Each selected g_j is a low derivative of an earlier or current generator, so its factorization recovers the next coordinate ideal and closes the induction. In particular no derivatives of order above Q are ever taken from (5), even though the theorem allows q above Q. Step 10 separately handles empty D, the unit ideal, and no essential variables, avoiding a spurious positive-degree base case.

Step 11 uses only what the implicit-calculus node states: coordinate derivations remain regular and commute with Taylor expansion. Its Fitting citation supplies base change for the finite presentations, including independence of regular generators. It does not use the coefficient-data existence theorem, which depends on this item. Step 12 uses the jet-diagram node's explicit Taylor fibre-dimension identity and its finite local set of diagrams, hence finite local sequence values. Those are statements of that node, including the extended interpretation at nonclosed points; I did not replace them with ordinary local-ring Hilbert--Samuel values. Step 13 uses only finitely many pivot opens and elementary residue-field Gaussian elimination. This ensures ranks cannot drop before the minors impose the reverse bound, and the finite separating indices from step 12 identify the whole equality germ.

I tested K=0, K=A, a single variable power z^d (the terminal low derivative gives (z), as does the relevant minors matrix), a smooth ideal generated by transverse coordinates, and f=z^2+w^3 with d=2 (both ideals are (z,w^2)). These checks catch the zero-rank, full-row-rank and nonreduced-stratum cases: the theorem is an ideal equality, not just an equality of radicals. The geometric clause asserts equality of sets/germs and uses the extended Taylor convention at nonclosed points. Every proof step is under 900 characters; none hides a long comparison or an existence claim. All five citations were copied verbatim into citations.json, and proof_deps is exactly the union of step uses. There is no off-unit statement use and no new dependency cycle.

## Unfinished work

No mathematical clause is left to split in this item. The cited existing statement nodes remain their own items as appropriate. The detailed BM source still needs to be obtained in the literature collection by the authorized maintainer. Delivery verification is performed by the required remote dry run.
