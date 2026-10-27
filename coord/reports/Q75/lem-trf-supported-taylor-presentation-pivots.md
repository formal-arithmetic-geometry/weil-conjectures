# Q75 stage-1 report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-supported-taylor-presentation-pivots.json`: split statement, eight complete proof steps; no Mathlib match for the whole item. The statement is unchanged.
- `citations.json`: one verbatim statement quotation for each node used by each proof step.
- `searches.jsonl`: actual search command records, retained unchanged.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. Elementary finite algebra is written in the proof; the non-elementary formal substitution, power-series unit test, and Fitting presentation/base-change facts already have nodes.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact blueprint tag, supported Taylor terminology, Taylor, and MvPowerSeries found no declaration stating this item. Polynomial Taylor declarations, analytic power series, and the formal-fibre p-derivation declarations do not state the supported presentation and pivot theorem. The item has no Lean audit indicating an existing proof.

## Wanted literature

WANTED: Bierstone--Milman, *Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant*, Invent. math. 128 (1997), 207--302, pp.263--268 (Lemma 7.7, Remark 7.11, Definitions 7.12--7.13 and Theorem 7.14), for lem-trf-supported-taylor-presentation-pivots. It is absent from literature/. I read the journal PDF online at https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf and did not download it. The local ILO text VIII 2.3.11--2.3.13, printed pp.93--94, gives the historical resolution route, not this algebraic proof. Accordingly proof_origin.by is agent. The Stacks part was read locally in more-algebra.tex, Tags 07Z8 (lemma-fitting-ideal), 07ZA(3) (lemma-fitting-ideal-basics), and the neighbouring minors lemma 07Z7.

## What was wrong or incomplete

The item was statement-only. The supported generation sentence in BM's final paragraph requires the downward-closure argument for the quotient supports: multiplying arbitrary Taylor polynomials by the f_i does not by itself prove that only supported columns suffice. Step 3 supplies the coefficient formula and that argument.

The claimed pivot is not obtained merely by counting columns. Steps 4--6 prove the truncated basis first, count it using the first-vertex partition, and identify its determinant with the diagram-row subdeterminant. No assumption that each homogeneous form is a monomial is used.

The stored blueprint ancestry is historical. I read the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`: its present route uses contracting correspondences, whereas this item's preserved ancestry descends from an older resolution branch. This split completes the dispatched algebraic input without changing that ancestry, the chapter, or the unit. Its split_report explicitly records this observation. No mathematical error in this item's statement was found; no STATEMENT-DISPUTED is required.

The inherited instruction to read coord/dag-sync.md points to a file absent in this live shared repository. The explicit current brief supplies the read-only clone and delivery procedure and takes precedence. No repository or launcher file was written, no git command was run, no compiler was invoked, and no agent was started.

## Searches and reuse

I read the item's earlier Q12 searches and retained all of them. I also ran Q75 searches using msearch.py: LeanFinder with both supported-Taylor-generation and filtered-basis wording, Loogle `MvPowerSeries, Matrix.det`, the grep `Taylor.*(pivot|presentation)|supported.*Taylor|Hilbert.?Samuel` in RingTheory, and LeanSearch for the whole supported finite-jet theorem. The log entries are the actual command records. LeanFinder's submersive-presentation hits concern polynomial Jacobian matrices. I opened `Algebra.PreSubmersivePresentation.isUnit_jacobian_of_linearIndependent_of_span_eq_top` in Mathlib/RingTheory/Extension/Presentation/Submersive.lean:165--174; it is a Jacobian-specific criterion and does not give the diagram-row basis or supported presentation here. LeanSearch returned analytic Taylor statements, a univariate polynomial translation, and MvPolynomial.basisRestrictSupport. They do not imply this result in one line. Loogle and the prescribed grep returned no hits. No new node therefore needs its own search.

Whole-DAG statement searches and blueprint_refs.py searches for Taylor, Fitting, substitution and binomial located the reusable nodes. In particular, lem-trf-formal-transverse-shift-calculus gives a more general formal substitution theorem; lem-weil-pbc-power-series-local-ring gives the exact unit test; lem-trf-fitting-ideal-independence-base-change gives the presentation-independent Fitting ideal and arbitrary scalar extension. I read their complete statements. I also examined the existing homogeneous-continuous-formal-division, supported-homogeneous-division, jet-diagram-hilbert-control, and formal-Hilbert-stratum-minors statements. Their stronger hypotheses or broader conclusions are unnecessary here. No new lemma duplicating any of these was made.

## Not duplicates

No new nodes. All three non-elementary inputs are reused by their existing ids. There are no new/existing same-tag pairs to adjudicate.

## What could not be finished

Nothing remains in this stage-1 split. The BM source is still wanted as a local literature artifact; its online text was read and the self-contained argument is supplied. The required delivery tools perform the server checks; their final result is reported by the dispatch answer.

## Review by Q75

I checked the item against the BM journal text on printed pp.265--268, especially the full Taylor relation matrix (7.12), presentation independence in Remark 7.11, and the supported relation matrix in the final paragraph of Theorem 7.14. I read ILO VIII pp.93--94 to distinguish the resolution reference from the actual algebraic argument, and read the Stacks 07Z8/07ZA source for the Fitting assertions. There are no new nodes whose sources require a separate review.

Step 1 uses exactly the continuous shift and coefficient formula in lem-trf-formal-transverse-shift-calculus. Its hypotheses hold with W=X, a fresh transverse tuple V of the same length, phi(W)=W in (W), and zero auxiliary variables; apply it to h(V), which is independent of W. I wrote the regrouping from the jointly completed ring to A[[Y]] explicitly, so no unsupported substitution into a general formal power series over A is assumed. Factorials are invertible because L has characteristic zero.

Step 2 is elementary ideal algebra: stability under Y_j follows from the explicit difference of two translates, and the truncated ring has finitely many monomials. It establishes the stronger A-span assertion rather than assuming that an ideal span and a module span agree.

Step 3 uses only the hypotheses and Step 1's homomorphism. I checked that Delta_i is downward closed by its definition; no upward closure is mistakenly used. The explicit binomial coefficient formula shows the shifted quotient still has Y support in Delta_i. The infinite X series is well-defined coefficientwise. Reduction modulo (Y)^{t+1} makes the final generating list finite. Reverse containment follows from Step 2. This proves both matrices really present the same F_t.

Step 4 uses the unique homogeneous division hypothesis for the full prefix, which is permitted by choosing its bound at least all d_i. I wrote the finite induction for spanning and the least-leading-degree argument for independence. No general filtered-basis theorem is being silently cited. Step 5 uses the elementary first-vertex partition and evaluation of the already established mutual expressions between the two finite column families. Its claim that the remaining columns vanish is only after X=0; the corresponding columns over A need not vanish.

Step 6 cites the exact constant-coefficient unit criterion (a) in lem-weil-pbc-power-series-local-ring, with coefficient field L a local ring. The complementary monomial columns have upper-right block zero and lower-right block identity even when the supported columns themselves have entries outside D. Expansion of the determinant proves the diagram-row submatrix is invertible at zero. This is the precise bridge from the basis to the specified pivot.

Step 7 uses both clauses of lem-trf-fitting-ideal-independence-base-change. Its statement uses arbitrary vectors in the kernel, so I explicitly supplied the multilinear determinant expansion to relate it to the finite column matrices. Transposition changes no generated ideal. The index calculation N_t-(H_t-1)=r_t+1 is written. F_t is finite because it is a quotient of A^{N_t}; no flatness or Noetherian hypothesis is required for the cited base-change statement. For H_t=0 I use only the out-of-range convention of def-trf-minor-ideal, not a negative-index Fitting theorem absent from the cited node.

Step 8 uses the same Fitting independence statement for an arbitrary new finite ideal generating list. I checked that its residue rank is the original r_t by mutual finite column expressions, so the indexed minors really have the same size. This avoids tacitly requiring the new generators to satisfy supported division. The determinant argument is not repeated for those arbitrary generators.

Small cases checked: K=0 with no vertices gives B with no columns, rank zero, empty pivot determinant 1, and Fit_{N_t-1}(A^{N_t})=0. A degree-zero vertex gives D=N^d, a unit generator, full rank and minors size N_t+1. With d=0, A=L and N_t=1: the only possibilities are the zero ideal and the unit ideal and both agree. For one variable with f=X^m, supported columns are the usual shifted powers; for t<m the pivot is empty and for t>=m it has t-m+1 columns. The generators' replacement may add redundant or zero generators without affecting the cokernel. Arbitrary A to A' can make the fibre rank drop; the statement fixes the original H_t index, as does the proof, and does not incorrectly recompute it after base change. I also checked t=0 and empty complements.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual files. No new statement-only wrapper rephrases a clause. Every cited node says what is taken from it and has a verbatim quote in citations.json. proof_deps is exactly the union of the uses lists. All non-elementary steps are shorter than 2000 characters. The elementary steps are explicit coefficient, partition or finite-degree arguments, not literature references used as proofs. The only off-unit input is the existing Mathlib leaf for the unit test, which is an allowed generic tool. The shift input has no dependency path back to this item. No SGA route is used.

Dry-run repair: the citation gate required a quote of at least 40 characters for Step 7; I replaced the short out-of-range clause with the entire verbatim minor-ideal statement. No proof or statement change was needed.
