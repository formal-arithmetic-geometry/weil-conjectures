# Q160 repair report: lem-trf-fs-chart-free-factorization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fs-chart-free-factorization.json`: statement unchanged byte for byte; six assembly steps, 2413 characters in total (latest repair).
- `dag/nodes/sec-trace-formula/lem-trf-lattice-monoid-minimal-determinant-tuple.json`: statement; unsplit; no Mathlib match. Extracts the Cauchy–Binet and well-ordering argument (old steps 3–4, 1135 characters).
- `dag/nodes/sec-trace-formula/lem-trf-integer-matrix-fractional-lattice-witness.json`: statement; unsplit; no Mathlib match. Extracts the adjugate, rational coordinates, and floor remainder argument (old step 5, 735 characters).
- `dag/nodes/sec-trace-formula/lem-trf-saturated-monoid-fractional-column-descent.json`: statement; unsplit; no Mathlib match. Extracts the common denominator, saturation, and column determinant argument (old step 6, 818 characters).
- `citations.json`: whole-statement verbatim quotations for every citation of every parent step. `searches.jsonl` is the genuine new msearch log. `repair.py`, `write_report.py`, and `ilo.txt` are sandbox-only working materials.

Three new nodes, all status unsplit with empty proof and proof_deps and null proof_origin; zero Mathlib leaves. Future workers can work on the three independent arguments concurrently. None restates the fs-chart theorem or a basis-existence clause: they respectively select a least nonsingular tuple without asserting it is a basis, produce an integral fractional remainder without monoids, and lower one determinant from supplied fractional data without asserting a tuple or basis exists.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, exists_fs_chart_free_factorization, fs-chart/free-factorization terminology, parallelepiped, and determinant-minimality found no project attachment. The existing `AlgebraicGeometry.exists_fs_chart_free_factorization` in `lean/Sheaf/AlgebraicGeometry/FsChartFreeFactorization.lean:81` has its whole proof `sorry` at line 105, so does not count as a finished proof.

## WANTED

None. All source ingredients are available locally. The minimal-determinant refinement remains explicitly attributed to an agent; ILO does not state this general theorem verbatim.

## Current landing-return repair (2026-10-23, returned head 0cca083f71d)

I resumed the retained delivery rather than discarding the approved work. The first required dry run completed with exit 0 and `OK (not pushed)` at 50a4b1e5563. I read the current return and released re-split order. Compared with the retained delivered copy, the current parent differs only in proof, proof_deps and split_report; its statement, source, ancestry, inherited searches, audit and review fields agree. I nevertheless rebuilt the parent from that current record and reapplied only those three owned fields, so the delivery overlay preserves all current inherited data. All three helper ids remain absent from the current DAG. The delivery command performs the fetch and fresh-base commit; no worker git operation is used.

I re-read the full current statements of def-trf-fs-log-blowup, lem-trf-fg-torsionfree-group-free and the three helper statements used by the assembly. Their current quotations still match every entry of citations.json. I also re-read the determinant definition, Cauchy–Binet and adjugate nodes supporting the helpers' preserved arguments, and the formal-Jacobian minor-expansion statements in the existing same-tag comparisons. No changed statement requires a replacement citation. The fs definition still states finite generation, injectivity into group completion and root saturation; the finite-group lemma still requires precisely the finite generation established in step 1 and torsion-freeness assumed by the item. I made a concrete assembly clarification in step 3: under the proper-span alternative explicitly choose an integer y outside the span, then apply the floor-witness node to that y. That node quantifies over such y, so this makes its hypothesis and application visible rather than treating it as an unconditional existential theorem.

I read the retained 19 actual Mathlib search results, including the unavailable LeanSearch responses and the invalid exploratory Loogle identifier diagnostic. The node statements and search questions are unchanged, so I did not repeat searches. I checked the returned hits in the current Mathlib source at CardQuotient.lean:85–103, ZLattice/Basic.lean:91–195 and Matrix/Determinant/Basic.lean:435: none gives a complete new helper by a one-line specialization. I re-read ILO VI Proposition 1.9, VI 3.7(a), VIII 3.1.17 and Stacks 0F0K/07DQ; the nodal example remains distinguished from the explicitly agent-written general refinement. Searching WeilConjectures again finds no finished attachment, and the existing Sheaf theorem still ends in sorry.

Against B–E, the helpers remain self-contained and statement-only, their distinct roles and same-tag comparisons remain valid, and every substantive parent input has a node whose statement supplies it. Rank zero bypasses the positive-rank helpers; A=(-2), y=1 gives a=1/2 and x=-1; columns (1,0),(1,2) with y=(0,1) give x=(1,1) and determinant descent from 2 to 1. The non-face diagonal chart and torsion-unit examples still meet the hypotheses without adding a face or torsion-free ambient-group assumption. All parent steps stay below 2000 characters and the assembly stays below 3000. This is a fresh delivery of the repaired split, retaining all previous reports and proofs below; earlier dry-run and push commits are historical.

## Repair of landing return at 0cca083f71d (2026-10-23)

The current return in coord/returns/Q160.md is dated 2026-10-22 16:44 UTC and names delivered head 0cca083f71d. I continued the retained four nodes, citations, 19 genuine search results and full earlier report. The first required dry run exited with four new same-tag comparisons, which are repaired below. I refreshed the parent from the current shared DAG and reapplied only proof, proof_deps and split_report. Its statement and other fields match the current parent exactly. All three helper ids are still absent from that DAG. The released stage-1 re-split order remains present and requires at least two helpers and assembly below 3000 characters; this delivery retains three helpers and 2377 characters. The delivery tool, rather than a worker git operation, builds the overlay on its freshly fetched current origin/sheaf-dag.

I re-read the complete current statements of every parent citation and the determinant definition used by each helper, plus the Cauchy–Binet and adjugate statements underlying the preserved helper arguments. All seven quotation records still match their cited statements verbatim and cover every parent citation. No mathematical citation changed. In step 2 I made n>0 explicit before the saturation calculation; this is the existing root-saturation condition, not an additional item hypothesis. I re-read the two current formal-Jacobian minor-expansion statements named by the dry run: neither constructs integer lattice tuples or proves monoid membership, so neither replaces either helper. Their four pairwise differences are recorded under Not duplicates.

I checked the retained source passages in ILO VI 1.9, VI 3.7(a) and VIII 3.1.17, and Stacks 0F0K/algebra-item-cauchy-binet and 07DQ/algebra-lemma-matrix-left-inverse. The parent remains explicitly an agent refinement of the particular nodal chart. The current WeilConjectures source search yields no finished attachment, and the Sheaf declaration still ends in sorry. I read the retained search log rather than repeating unchanged questions. The earlier edge-case calculations remain valid: rank zero bypasses the rank-positive helpers, the determinant-two example produces an integral fractional remainder, and a negative rank-one determinant gives the same strict absolute-determinant descent. No current proof step exceeds 2000 characters.

## Repair of latest landing return at 8e3d0d7fc27

The interrupted push was completed successfully: retained push-repair.exit is 0 and push-repair.log records head 8e3d0d7fc27. The current maintainer return at 2026-10-22 12:15 UTC explicitly names that head, so this is a subsequent landing-return repair, not a retry of an unfinished push. No earlier delivery process was still active. I first ran the required dry run on the retained split; it exited 0 and passed server preflight at 555d3348b4b.

I compared the retained delivered parent with the current read-only DAG again. The only differing fields were proof, proof_deps, and split_report. I refreshed the parent from that current record and reapplied exactly these three stage-1 fields, adding this latest repair provenance. Its statement and every maintainer-owned field remain current. The three new helper ids are still absent from the live DAG, and the released stage-1 repair order still requires at least two new tasks and assembly below 3000 characters. The delivery command builds a fresh commit on its newly fetched origin/sheaf-dag.

I re-read the complete current statements of def-trf-fs-log-blowup, lem-trf-fg-torsionfree-group-free, def-weil-pbc-matrix-determinant, lem-weil-pbc-cauchy-binet, and lem-weil-pbc-matrix-adjugate-identity, along with all three retained helper statements. None requires a changed mathematical citation. The fs definition explicitly supplies finite generation, the injective canonical map and root saturation; the finite-group-basis node is a Mathlib leaf with precisely the finite-generation/torsion-free hypotheses used. The determinant definition, rectangular Cauchy–Binet identity and adjugate identity still give exactly the preserved helper arguments. All parent citation quotes were checked against the current statements and remain verbatim. The assembly still has six steps and 2367 characters, with no doubled TeX backslashes and no step above 2000 characters. All three helpers remain self-contained, statement-only tasks. No unchanged Mathlib search was repeated; I read the 19 retained logged search results, including the explicitly unavailable LeanSearch results.

The source checks were repeated at Stacks 0F0K/algebra-item-cauchy-binet and 07DQ/algebra-lemma-matrix-left-inverse, and ILO VIII 3.1.17. The upstream project search again gives no exact finished attachment; the Sheaf theorem remains sorry. The rank-zero bypass, rank-one negative determinant, determinant-two fractional remainder, non-face diagonal monoid map and torsion-unit cases in the signed review still apply unchanged. No hypothesis was added or conclusion altered. After this report and provenance update, I will run the final dry run and push only once it exits successfully.

## Repair of landing return at 48cf4b45ff7

The latest return approves the mathematics but rejects the old side-project completion because it was not promoted to the live DAG. I continued the four retained node files, report, citations and 19 actual search-log entries. I compared the retained item against the current shared DAG: only proof, proof_deps and split_report differed. I refreshed the item from the current DAG and reapplied those stage-1 fields, preserving the current statement, ancestry, previous reviews, Lean statement and audit metadata. The three helper ids remain absent from the current DAG. The released stage-1 repair note still requires the same three-task re-split. The delivery tool fetches origin/sheaf-dag and builds a fresh commit against that current base; the old delivered commit is not re-pushed.

I re-read the current full statements of def-trf-fs-log-blowup and lem-trf-fg-torsionfree-group-free, and all three retained helper statements. The live fs definition still gives exactly finite generation, the embedding into group completion and root saturation used in parent steps 1, 2 and 6. The group-basis statement is now marked mathlib and gives exactly the finite basis needed in step 1. Every retained parent citation quote is still verbatim in its current statement. I also re-read def-weil-pbc-matrix-determinant (each helper's statement dependency), lem-weil-pbc-cauchy-binet and lem-weil-pbc-matrix-adjugate-identity: their determinant, rectangular-minor and adjugate formulas still support the preserved original helper arguments. Thus no replacement citation or changed hypothesis is needed. None is merged. Steps 3--6 continue to use the same rank-positive lattice hypotheses and rank-zero bypass checked in the signed review.

I re-read ILO VI Proposition 1.9, VI 3.7(a), VIII 3.1.17 and Stacks 0F0K/07DQ at the retained source locations. The parent remains explicitly an agent-supplied general algebraic refinement; no general assertion is attributed verbatim to the special nodal chart. Project-source searches still found no finished upstream attachment; the Sheaf declaration ends in sorry. The genuine search log and the helper Mathlib verdicts are retained without repeating unchanged search questions. Rechecking B--E found no new statement dispute, missing hypothesis, hidden long step or changed source requirement.

The fresh dry run before this report update exited 0 and passed the server preflight at f309a494f3f. I will rerun after this rebase record and push the resulting fresh delivery. This section records the current landing-return repair; earlier validation commits below are historical.

## Return repaired and retained work

The return requires spreading the old 5728-character proof into at least two separately workable statement-only nodes, with parent assembly at most 3000 characters. This delivery creates three comparably sized argument tasks and leaves 2367 characters in the parent. The item statement, inherited mathematical search records, source, provenance, and ancestry are preserved. No statement dispute arose. The previous report's decision to keep these short arguments inline is superseded by the human's explicit 2026-10-21 re-split instruction.

The sandbox initially contained only dispatcher brief markers, with no node, report, citations, or search log. I copied the live repository's returned version, whose nine proof steps exactly match the return's lengths. I read the inherited search results and the repository's Q10 stage-1 report. That report and every original proof step are preserved verbatim in the appendices below; the original log file was not present and no searches were invented to replace it. New helper statements have newly run, logged searches.

Coverage of the old argument:

| Old step | Where its full argument now lives |
|---|---|
| 1: quotient, finite generation, arbitrary finite free basis | Parent step 1. |
| 2: saturation of image by n(x+g(b)) | Parent step 2, with the same displayed identity and hypotheses. |
| 3: generator matrix B, integer right inverse C, BC=I, rectangular Cauchy–Binet, m>=r | New minimal-determinant tuple task; original argument retained below for that worker. |
| 4: least positive integer determinant | Same new tuple task; original well-ordering argument retained below. |
| 5: adjugate inverse, independence, b,z,a,x, some positive fractional coefficient | New fractional-witness task, whose statement includes the explicit floor formulas; original argument retained below. |
| 6: denominator, saturation, replacement matrix AE, Leibniz det(E)=a_j, strict descent | New fractional-column-descent task; full original calculation retained below. |
| 7: integer spanning and independence, lift each basis vector from S to Q | Parent steps 3–4. |
| 8: kernel and surjectivity of Phi, including r=0 | Parent step 5. |
| 9: nonnegative coefficients, h restricts to g, injectivity, product group-completion universal property | Parent step 6. |

The three new nodes contain only self-contained statements. Their proofs are deliberately not filled: the complete old argument is retained in the report rather than embedded as a proof sketch in a supposedly unsplit statement. Together they are strictly below the parent; no new node has a dependency on the parent or on another new node. The elementary quotient saturation and final universal-property calculation remain explicit parent steps rather than becoming artificial extra nodes.

## Sources and duplicate searches

I read ILO Exposé VI Proposition 1.9 and its proof, printed pp. 70–71: its specific nodal monoid chart has injective map with group cokernel Z. I read VI 3.7(a), printed p. 75, for the finite torsion-free group context, VIII 3.1.1–3.1.2, printed p. 98, for monoid conventions, and VIII 3.1.17, printed p. 101, for root saturation. These provide the background and conventions; the general algebraic refinement is agent-written. The source's internal references to SGA are not inputs to this algebraic proof.

For the first new node I read Stacks Tag 0F0K, algebra-item-cauchy-binet, `algebra.tex:282–288`, and the existing Cauchy–Binet and determinant statements. For the second I read Tag 07DQ, algebra-lemma-matrix-left-inverse, `algebra.tex:2680–2703`, in particular the explicit adjugate identity, and the existing adjugate node's entire statement. For the third I read 0F0K again, the determinant's permutation formula, and the root saturation convention in ILO VIII 3.1.17. Its conclusion about x lying in S requires the denominator argument, not just a determinant lemma. No new source theorem is being misattributed to either tag.

Before creating the nodes I searched all `dag/nodes` for parallelepipeds, least/minimal determinants, fractional lattice points, column replacement, root saturation, saturated rational combinations, and the source tags. I also searched the whole imported blueprint using blueprint_refs.py for parallelepiped, determinant, lattice, column, monoid, nonzero determinant, fractional, and saturated additive. I read the nearby maximal-minor, face-sharpening, Cramer, determinant-column, and minor/Popescu statements. None gives a complete proposed helper; precise same-tag differences follow below. The blueprint ancestor command gives lem-trf-local-term-locality; each new from.via prepends the present item to its existing ancestry. same_as remains []. The current main-20261015 locality proof follows the contracting-correspondence route; this auxiliary algebra remains in its recorded historical nodal-chart ancestry and changes no chapter or unit route or realization fields.

## Mathlib searches

All new-node Mathlib searches were made only through the required msearch.py command. For each node I ran two semantic phrasings with LeanFinder, a Loogle query and local Mathlib grep, plus LeanSearch. LeanSearch returned a rate-limit error for all three queries and is recorded as unavailable, never as no match. Loogle `fundamentalDomain, Matrix` returned an unknown-identifier diagnostic, so I made the valid follow-up query ZSpan.fract_mem_fundamentalDomain and did not infer absence from the invalid pattern.

The first task's hits AddSubgroup.index_eq_natAbs_det and Submodule.natAbs_det_basis_change were read at Mathlib/LinearAlgebra/FreeModule/Finite/CardQuotient.lean:85–103: they assume already supplied bases of subgroups, not a tuple within a given submonoid, and make no minimizing choice. Results about total unimodularity or diagonal dominance add hypotheses absent here. The second task's ZSpan.fract_mem_fundamentalDomain, ZSpan.floor and fractional part results were read at Mathlib/Algebra/Module/ZLattice/Basic.lean:91–195: they supply part of the argument after a basis is given but do not establish rational independence from an integer matrix and the integral nonzero remainder together. The third task's Matrix.det_updateCol_sum was found by Loogle, located by logged grep at Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:435, and read through line 439. It proves only the determinant formula; root-saturated monoid membership after clearing rational denominators is additional work. I also read the generated additive NSMulSaturated convention in GroupTheory/Subgroup/Saturated.lean:24–37. FixedDetMatrices.reduce, returned by the second phrasing, concerns a different 2-by-2 transformation. Thus none of these tasks is an exact or one-line Mathlib specialization.

## Not duplicates

lem-trf-lattice-monoid-minimal-determinant-tuple vs lem-trf-formal-jacobian-coordinate-minor-expansion: the existing node computes quotient-Jacobian minors after changing formal coordinates; the new node selects a least positive absolute determinant among tuples in an integer additive monoid generating the lattice. The existing statement gives neither this lattice construction nor its monoid conclusion.

lem-trf-lattice-monoid-minimal-determinant-tuple vs lem-trf-formal-jacobian-generator-minor-expansion: the existing node computes quotient-Jacobian minors after replacing a list by formal power-series linear combinations; the new node selects a least positive absolute determinant among tuples in an integer additive monoid generating the lattice. The existing statement gives neither this lattice construction nor its monoid conclusion.

lem-trf-saturated-monoid-fractional-column-descent vs lem-trf-formal-jacobian-coordinate-minor-expansion: the existing node computes quotient-Jacobian minors after changing formal coordinates; the new node proves membership of an integral rational combination in a root-saturated integer monoid and strict determinant descent on column replacement. The existing statement gives neither this lattice construction nor its monoid conclusion.

lem-trf-saturated-monoid-fractional-column-descent vs lem-trf-formal-jacobian-generator-minor-expansion: the existing node computes quotient-Jacobian minors after replacing a list by formal power-series linear combinations; the new node proves membership of an integral rational combination in a root-saturated integer monoid and strict determinant descent on column replacement. The existing statement gives neither this lattice construction nor its monoid conclusion.

lem-trf-integer-matrix-fractional-lattice-witness vs lem-weil-pbc-matrix-adjugate-identity: states the adjugate matrix identities only; it does not supply the integral floor remainder or a positive fractional coordinate.

lem-trf-integer-matrix-fractional-lattice-witness vs lem-weil-pbc-matrix-left-inverse-minors: states ideal membership and scalar matrix inverse criteria over a general ring, not a point in a proper integer column sublattice.

lem-trf-integer-matrix-fractional-lattice-witness vs lem-weil-pbc-popescu-translated-presentation-data: gives translated presentation data and evaluated Jacobian minors, not fractional integer lattice points.

lem-trf-integer-matrix-fractional-lattice-witness vs lem-weil-pbc-popescu-translated-presentation-properties: concerns constant coefficients and Jacobian minors of a ring presentation, not integer lattice remainders.

lem-trf-integer-matrix-fractional-lattice-witness vs lem-weil-pbc-popescu-translated-presentation: constructs a translated algebra presentation with Jacobian ideal conditions, not an integer lattice remainder.

lem-trf-lattice-monoid-minimal-determinant-tuple vs def-weil-pbc-matrix-determinant: defines the determinant, without any tuple selection, lattice-point, or monoid membership theorem.

lem-trf-lattice-monoid-minimal-determinant-tuple vs lem-weil-pbc-cauchy-binet: states the rectangular determinant identity only, not a monoid-constrained minimum or root-saturation membership.

lem-trf-lattice-monoid-minimal-determinant-tuple vs lem-weil-pbc-det-column-permutation: permutes existing columns and computes the sign; it neither selects tuples nor replaces a column by a fractional integral combination.

lem-trf-lattice-monoid-minimal-determinant-tuple vs lem-weil-pbc-det-repeated-column-zero: annihilates a determinant with repeated columns and gives none of the new existence or saturation conclusions.

lem-trf-saturated-monoid-fractional-column-descent vs def-weil-pbc-matrix-determinant: defines the determinant, without any tuple selection, lattice-point, or monoid membership theorem.

lem-trf-saturated-monoid-fractional-column-descent vs lem-weil-pbc-cauchy-binet: states the rectangular determinant identity only, not a monoid-constrained minimum or root-saturation membership.

lem-trf-saturated-monoid-fractional-column-descent vs lem-weil-pbc-det-column-permutation: permutes existing columns and computes the sign; it neither selects tuples nor replaces a column by a fractional integral combination.

lem-trf-saturated-monoid-fractional-column-descent vs lem-weil-pbc-det-repeated-column-zero: annihilates a determinant with repeated columns and gives none of the new existence or saturation conclusions.

lem-trf-lattice-monoid-minimal-determinant-tuple vs lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor: the existing node selects a nonsingular minor over a field from an injective matrix; it does not minimize the absolute determinant over all tuples in an additive monoid.

lem-trf-integer-matrix-fractional-lattice-witness vs lem-sfb-matrix-cramer-determinant-identities: Cramer's determinant identities provide algebraic formulas, with no proper integer sublattice, floor reduction, or nonzero integral remainder.

lem-trf-saturated-monoid-fractional-column-descent vs lem-sfb-matrix-cramer-determinant-identities: a column determinant formula does not imply that a fractional integral combination belongs to a root-saturated monoid.

All three vs lem-trf-fs-chart-free-factorization: none supplies elements of Q lifting a cokernel basis or the injective fs chart and its group completion. The parent retains quotient saturation, the minimum contradiction, lifting, and the complete verification of the factorization. All three vs lem-trf-fs-face-sharpening: that node concerns localization along a face and a sharp quotient; no face hypothesis appears in these lattice lemmas, and it does not give their minimizing, fractional, or determinant conclusions.

## Review by Q160

For this resumed landing-return repair I re-read all current parent citations and helper statement dependencies, checked their exact quoted clauses, and checked the retained source arguments and small cases as recorded in Current landing-return repair above. Step 3 now explicitly chooses the outside vector required by the universally quantified lattice-witness statement. The parent is refreshed from the current DAG with only its three stage-1 fields reapplied; no inherited statement or maintainer-owned record is replaced. The resumed initial dry run passed before this clarification, and the final dry run is rerun on these exact files.

For the return naming 0cca083f71d, I re-read all current citation statements and the four new same-tag pairs reported by the resumed dry run. The minor-expansion nodes have power-series/Jacobian hypotheses and conclusions, whereas the retained helpers have integer-lattice and monoid hypotheses and conclusions, as detailed above. Step 1 still checks finite generation and torsion-freeness before applying the finite-basis node; step 2 now states the positive multiplier explicitly; step 3 applies the three helper statements with exactly the established finite-generation, nonzero-determinant and root-saturation hypotheses. Steps 4–6 still prove the lift, kernel, surjectivity and product-completion properties directly. I refreshed all inherited parent fields from the current DAG, retained the reviewed mathematical route, and repaired the actual new duplicate-check diagnostics.

For the latest return naming head 8e3d0d7fc27, I repeated the current-statement reading and quotation check described above. Parent steps 1 and 2 still use exactly finite generation and root saturation from the fs definition; step 3 still receives every hypothesis required by the three helper statements, and steps 4--6 still establish the basis lifts, kernel/surjectivity and product group-completion property explicitly. The latest return changes the landing base, not the mathematics. I refreshed the parent record, retained the existing three argument tasks, and recorded this distinct return so the new delivery is reviewable against its actual returned head.

I checked delivery-errors B–E against the actual four delivered node files, the complete statements of every cited existing node, the relevant ILO paragraphs, and both Stacks tagged locations. There is no source statement dispute and the parent statement is exactly the returned statement. Each new node introduces all objects, includes its integer/rational ambient group and determinant convention, and states its own hypotheses rather than referring to a setting constructed elsewhere. Proofs, proof dependencies and proof origins on new nodes are empty as required. I reviewed all shared-tag candidates above; the reusable determinant facts remain existing nodes, whereas the three new tasks ask for genuinely additional lattice or saturation constructions. The parent's inherited metadata is preserved; only stage-1 owned fields are changed.

Parent step 1 cites def-trf-fs-log-blowup for finite generation, canonical group completion and integrality: its statement explicitly says a fine saturated monoid is finitely generated, embeds in its completion, and is root saturated. It cites lem-trf-fg-torsionfree-group-free for a finite integer basis: that statement assumes exactly finite generation and torsion-freeness. Finite generation of L is established from differences of the monoid generators before applying it, and torsion-freeness is the item's hypothesis. No basis is yet claimed to lie in S.

Step 2 cites only the root-saturation clause of def-trf-fs-log-blowup and writes the quotient-image calculation. Here n>0, q,g(a),g(b) all lie in Q, x+g(b) lies in Q^gp, and n-1 is nonnegative. Thus saturation applies in its correct ambient group; no torsion-freeness of Q^gp and no face condition is smuggled in.

Step 3 uses exactly the three new statements. The first receives r>0, additive S and the finite generating family already obtained in step 1, and gives a tuple minimizing its positive absolute determinant. The second receives that integer square matrix with nonzero determinant and supplies unconditional rational independence plus, under the proper-span alternative, the integral x and rational a with the required inequalities. The third receives the same S, root saturation from step 2, columns in S, and exactly those rational coefficients and integral x; its strict determinant decrease contradicts the first lemma's minimum over the same tuples. I read each new statement after writing the assembly to verify that no detail was borrowed only from an intended proof. The citations file quotes their whole statements verbatim, including independence, integrality, and strict decrease. Rank zero bypasses all three, as their hypotheses require positive rank.

Step 4 uses only the conclusions of step 3 and the definition S=pi(Q). Rational independence gives integer independence, and integer spanning therefore gives unique coordinates. The q_i lifts need no monoid section or extra existence theorem. Step 5 proves both directions of the group isomorphism: the quotient basis kills the m coordinates in the kernel, injectivity of g^gp kills u, and the remainder after subtracting a basis lift is literally in the image subgroup H, giving surjectivity. This argument remains valid at r=0.

Step 6 cites def-trf-fs-log-blowup for embeddings and the presented group completion, and proves the product universal property directly by the restrictions to P and coordinate generators. It verifies that nonnegative coefficients land in Q, that h restricts to g, and that injectivity follows from Phi and the canonical embeddings. This identifies h^gp with the very same Phi, rather than an unrelated abstract isomorphism. Steps 2, 4, 5 and 6 are direct definition/universal-property calculations; the only substantial lattice arguments are now the three unsplit tasks. Every new task and every parent non-elementary step is below 2000 characters, and the parent total is below 3000.

For each new task I also checked its intended proof, retained in the appendix. For the minimum tuple, B is r by m and C is m by r over Z, BC=I; the full rectangular Cauchy–Binet convention includes m<r, excluding the empty-sum case. The well-ordering is over positive integer absolute determinants. For the floor witness, the adjugate identity over Q gives a genuine inverse since the determinant is nonzero; z is an integer vector, x=y-Az is integral, and a=0 would imply y is in the excluded integer span. For column descent, take a positive common denominator N and nonnegative integers Na_i; Nx is a sum of monoid elements, so root saturation gives x in S. The replacement matrix has integer columns even though E and a are rational. Computing the determinant of E from the permutation formula gives a_j with no missing sign, hence the strict inequalities. These are the old arguments, now assigned to separate workers rather than silently removed.

Small cases: r=0 has empty basis and only the quotient-kernel argument; P=Q=0 and g=id have h=g. For r=1, S equal to the additive monoid generated by 2 and 3 is a valid input to the first lemma: these generators span Z as a group, and the minimum positive determinant is 2. This monoid is not saturated and contains no Z-basis, demonstrating that the first task asserts neither a basis nor saturation. With S=Z and A=(-2), y=1 gives b=-1/2, z=-1, a=1/2, x=-1, and the replacement determinant is -1. With A columns (1,0),(1,2) and y=(0,1), the floor remainder is x=(1,1), with a=(1/2,1/2), and replacing either column gives determinant 1. With A=I, there is no outside y, so the fractional-witness assertion is correctly conditional. Without root saturation, S generated by 2 and 3 and A=(2) would have x=1 excluded from S; this shows why the third lemma requires saturation. The saturated group S=Z^r and non-sharp monoids cause no positivity-of-coordinate issue: only fractional coefficients are nonnegative. For P=N -> Q=N^2 with 1 mapping to (1,1), the image is not a face but S=Z, so step 2 works exactly as written. Q=N times Z/2 with P=Z/2 as the units shows that torsion in Q^gp is harmless when L is torsion free.

Corrections made in this repair are the three extra independent tasks and the short explicit parent assembly; I also replaced the invalid exploratory Loogle pattern by a valid query when examining the second task. No source-tag error, missing hypothesis, circular dependency, off-unit proof tool, or longer hidden comparison was left. All new queries match the actual recorded log. No Lean source, repository file, launcher script, compiler, or build tool was changed or run.

## What could not be finished

The three new lemma proofs are intentionally deferred as statement-only stage-1 tasks under the return instruction. No part of the requested one-level re-split is omitted.

## Delivery validation

The required `deliver.py Q160 lem-trf-fs-chart-free-factorization --no-push` exited 0 and printed `OK (not pushed)` at b3dcddb1c61, with server preflight passed. The preliminary server review_split check also exited successfully. Sandbox consistency checks confirmed the unchanged parent statement, three unsplit helpers, the 2367-character parent proof, exact proof-dependency unions and all verbatim citation quotes. The delivery command performs its required preflight again on push.

## Preserved original arguments (verbatim)

### Old step 1

Put $G=Q^{\rm gp}$, $H=g^{\rm gp}(P^{\rm gp})$, and let $\pi:G\to L=G/H$ be the quotient. Identify $P,Q$ with their images in their group completions, as permitted by integrality in [def-trf-fs-log-blowup]. Set $S=\pi(Q)\subseteq L$. Choose finitely many monoid generators of $Q$; their images generate $S$ as a monoid and $L$ as a group, because every element of $G$ is a difference of elements of $Q$. Thus $L$ is a finitely generated abelian group. It is torsion free by hypothesis, so [lem-trf-fg-torsionfree-group-free] supplies a finite $\mathbf Z$-basis $e_1,\ldots,e_r$. Use its coordinates to identify $L$ with $\mathbf Z^r$.

### Old step 2

The image monoid $S$ is saturated in $L$. Indeed, suppose $n\ell\in S$ with $n\geq1$. Choose $x\in G$ lifting $\ell$ and $q\in Q$ with $\pi(q)=n\ell$. Since $nx-q\in H$, there exist $a,b\in P$ with $nx=q+g(a)-g(b)$. Consequently
$$n(x+g(b))=q+g(a)+(n-1)g(b)\in Q.$$
Saturation of $Q$ in $G$ [def-trf-fs-log-blowup] gives $x+g(b)\in Q$. Its image is $\ell$, proving $\ell\in S$. This calculation uses no assumption that $g(P)$ is a face and no torsion-freeness of $G$.

### Old step 3

If $r=0$, $L=0$ and its empty basis already lies in $S$; proceed to Step 8. Suppose $r>0$. Let $s_1,\ldots,s_m$ be the chosen generators of $S$ and let $B$ be the $r\times m$ integer matrix of their coordinates. Since they generate $L$ as a group, express each $e_j$ as an integer combination of the $s_i$. These expressions give an $m\times r$ integer matrix $C$ with $BC=I_r$. Apply [lem-weil-pbc-cauchy-binet]:
$$1=\det(BC)=\sum_{|T|=r}\det(B^T)\det(C_T).$$
Here $\det I_r=1$ follows directly from [def-weil-pbc-matrix-determinant]. Some summand is nonzero, so some ordered $r$-tuple of elements of $S$ has nonzero integer determinant. This also shows $m\geq r$, since otherwise the sum would be empty.

### Old step 4

Among all integer matrices whose $r$ columns belong to $S$ and whose determinant is nonzero, choose $A$ for which $D=|\det A|$ is least. Step 3 makes this set nonempty; its absolute determinants are positive integers, so the well-ordering of $\mathbf N$ supplies the least one. Determinants are integers by the finite sum of signed products in [def-weil-pbc-matrix-determinant]. Write $v_1,\ldots,v_r\in S$ for the columns of $A$.

### Old step 5

By [lem-weil-pbc-matrix-adjugate-identity] over $\mathbf Q$, the matrix $A$ has inverse $\operatorname{adj}(A)/\det A$. In particular its columns are independent and every rational vector has unique rational coordinates in these columns. If their integer span were a proper subgroup of $\mathbf Z^r$, choose $y\in\mathbf Z^r$ outside it. Put $b=A^{-1}y\in\mathbf Q^r$, let $z_i=\lfloor b_i\rfloor\in\mathbf Z$ (the unique integer with $z_i\leq b_i<z_i+1$), and set
$$a_i=b_i-z_i,\qquad x=y-Az=Aa\in\mathbf Z^r.$$
Thus $0\leq a_i<1$. Not all $a_i$ vanish, since otherwise $y=Az$ would be in the integer span. Choose $j$ with $0<a_j<1$. These formulas explicitly produce the lattice point; no fundamental-domain theorem is being assumed.

### Old step 6

Choose a positive common denominator $N$ of the finitely many rational numbers $a_i$. Then $Na_i\in\mathbf N$ and
$$Nx=\sum_i(Na_i)v_i\in S.$$
The saturation proved in Step 2 gives $x\in S$. Let $E$ be the rational identity matrix with column $j$ replaced by the vector $a$. Then $AE$ is $A$ with column $j$ replaced by $x$. The square case of [lem-weil-pbc-cauchy-binet] gives $\det(AE)=\det A\det E$. In the Leibniz sum [def-weil-pbc-matrix-determinant] for $E$, all columns except $j$ force the permutation to fix their indices, hence also $j$; the only surviving term is $a_j$. Therefore
$$0<|\det(AE)|=a_jD<D.$$
The matrix $AE$ has integer entries (its columns are $v_i$ and $x$), and all its columns belong to $S$. This contradicts the minimality of $D$. Thus the proper-span alternative of Step 5 is impossible.

### Old step 7

Consequently the $v_i$ generate $\mathbf Z^r$ over $\mathbf Z$. They are independent by Step 5, so every element has a unique integer expression in the $v_i$. They are therefore a $\mathbf Z$-basis of $L$ lying in $S$. For each $i$ choose $q_i\in Q$ with $\pi(q_i)=v_i$, which is possible by the definition $S=\pi(Q)$. In rank zero make no choices. This proves the asserted basis-lifting clause.

### Old step 8

Define the group homomorphism
$$\Phi:P^{\rm gp}\oplus\mathbf Z^r\to Q^{\rm gp},\qquad(u,(m_i))\mapsto g^{\rm gp}(u)+\sum_i m_iq_i.$$
If $\Phi(u,m)=0$, applying $\pi$ and using uniqueness of the basis coordinates gives $m=0$; injectivity of $g^{\rm gp}$ then gives $u=0$. Conversely, for $t\in Q^{\rm gp}$, write $\pi(t)=\sum_i m_i v_i$. Then $t-\sum_i m_iq_i\in H$, so it equals $g^{\rm gp}(u)$ for some $u$. This proves surjectivity and hence that $\Phi$ is an isomorphism. If $r=0$, the same argument says precisely that $g^{\rm gp}$ is an isomorphism, since its cokernel is zero.

### Old step 9

Restrict $\Phi$ to $P\oplus\mathbf N^r$. Its values lie in $Q$, because $g(p)$ and all $q_i$ lie there and the coefficients are nonnegative. The result is exactly $h$ in the statement, and its restriction along $p\mapsto(p,0)$ is $g$. The inclusions $P\hookrightarrow P^{\rm gp}$ and $Q\hookrightarrow Q^{\rm gp}$ are injective by integrality [def-trf-fs-log-blowup], as is $\mathbf N^r\hookrightarrow\mathbf Z^r$. Hence equality of two $h$-values gives equality of their $\Phi$-values and then equality of the inputs, proving that $h$ is injective. Group completion of the product $P\oplus\mathbf N^r$ is $P^{\rm gp}\oplus\mathbf Z^r$: a homomorphism from the product into an abelian group is uniquely the sum of its restrictions to $P$ and the $r$ coordinate generators, with the former extending to $P^{\rm gp}$ and each latter generator allowing integer multiples. Under this identification, the induced $h^{\rm gp}$ is $\Phi$, already proved an isomorphism.

## Preserved Q10 report (verbatim)

# Q10 stage-1 report: lem-trf-fs-chart-free-factorization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fs-chart-free-factorization.json`: statement, split; nine proof steps; statement unchanged; fresh Mathlib search records appended while retaining all inherited search records and provenance.
- New nodes: none. New Mathlib leaves: none. The existing finite torsion-free group basis, determinant definition and adjugate identity are Mathlib leaves; the existing general Cauchy–Binet node is reused as a tool.
- `citations.json`: one verbatim statement quotation for every node used by every numbered proof step.
- `report.md`: this report. `searches.jsonl` is the genuine msearch.py log. `scratch/` contains the source extraction and the local writing script, not delivery nodes.

There was no previous item copy or report in the sandbox, only dispatcher brief files. I copied the current repository node, retained its statement, source, inherited searches, created record and blueprint ancestry, and supplied its missing proof.

## Attachments

None. Searches of the read-only slopmaster2 and master project sources by the exact id, chart factorization, saturated monoid, group completion and cokernel/basis terminology found no project declaration giving this item. The exact node id is also absent from the upstream-name index. The log/toric chart notions used here are not formalized by a project theorem with these clauses. Abstract Grothendieck-group declarations do not lift a basis into Q, and sorry declarations in master would not qualify in any event.

## WANTED

None. The source material and elementary arithmetic needed for this algebraic refinement are present.

## What was missing and what changed

The item had an empty proof and explicitly called its general chart factorization an agent-supplied refinement of ILO VI Proposition 1.9. I read that proposition and its proof, printed pp. 70–71: it constructs a particular nodal monoid pushout and says that its chart map is injective with group cokernel Z. It does not assert the general basis-lifting claim as a theorem. I therefore preserved that distinction and marked the new proof as agent-written, with the precise source ingredients stated. I also read ILO VIII 3.1.1–3.1.2 (localization and sharpening), VIII 3.1.17 (saturation), and VI 3.7(a) (finite torsion-free group basis), rather than attributing the new minimal-determinant argument to those paragraphs.

The key extra argument is that S = image(Q -> Q^gp/g(P^gp)) is saturated. It is important here that the kernel subgroup comes from elements of Q: for nx=q+g(a)-g(b), the identity n(x+g(b))=q+g(a)+(n-1)g(b) puts the right hand side in Q. This allows saturation of Q to apply. No assumption that g(P) is a face, and no torsion-freeness of Q^gp, has been inserted.

The finite free group theorem alone does not give basis vectors in S. The proof chooses a tuple from S of least positive absolute determinant. If it fails to span the integer lattice, an integer vector outside its span has rational coordinates in that tuple. Subtracting the floors produces an integer vector with coordinates in [0,1), not all zero. Clearing their finite denominators and using saturation puts that vector in S. A column replacement then contradicts the minimal determinant. The final steps lift these basis vectors to Q and explicitly check the kernel, surjectivity, restriction to the monoid and identification of the induced group map.

The current blueprint's sk-i-curve-zero unit and lem-trf-local-term-locality proof follow the contracting-correspondence/normal-cone route. This node belongs to an already recorded historical nodal-chart ancestry. I did not change the chapter, unit, ancestor, or that route, and make no new unit-realization claim.

## Mathlib and duplicate searches

Before creating any auxiliary node I searched the whole DAG and blueprint for the full item, saturated monoids, lattice bases, fundamental parallelepipeds, integer matrices, determinant descent, column replacement, Cauchy–Binet, and the determinant declaration names; I also searched project Lean sources. Blueprint_refs ancestor returns lem-trf-local-term-locality. Blueprint search found no equivalent blueprint statement; same_as stays [].

All fresh Mathlib requests were run through the required msearch.py command and their exact queries and machine summaries are in searches.jsonl. Two semantic phrasings of the item returned only abstract group completions, unconstrained bases and monoid quotient maps, not this factorization. These searches are appended to the item's inherited records. Loogle's unquoted GrothendieckAddGroup identifier was unknown to that service; I report the error and do not treat that result as evidence of absence. The second semantic phrasing found Module.basisOfFiniteTypeTorsionFree', which is exactly the existing lem-trf-fg-torsionfree-group-free and is reused.

I investigated whether the rational-coordinate rounding/determinant descent needed an unsplit lattice lemma. Searches returned ZSpan.fract_mem_fundamentalDomain, ZSpan.floor and related fundamental-domain results; I read Mathlib/Algebra/Module/ZLattice/Basic.lean lines 90–195. They do not by themselves assert this monoid-constrained basis result. The requisite floor calculation is only the explicit identities in Step 5 after applying the already existing adjugate node, so no lattice node was created.

Further logged semantic searches and a quoted Loogle query found Matrix.det_updateCol_sum; the required grep located it at Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:435, and I read its statement and proof at lines 432–439. It states det(A with column j replaced by sum c_i A_i)=c_j det A. However it is also two lines from the existing Cauchy–Binet statement: the replacement matrix is AE for an identity matrix E with column j replaced by c, the square case gives det(AE)=det A det E, and the defining permutation sum gives det E=c_j. Under the brief's no-new-elementary-node rule I wrote that calculation in Step 6 and created no determinant node. The non-square Cauchy–Binet statement is also exactly what Step 3 needs to extract a nonsingular tuple from generators spanning the group. Its literal source is Stacks Tag 0F0K, algebra-item-cauchy-binet; I read that item in algebra.tex. I read the adjugate calculation in Stacks Tag 07DQ, algebra-lemma-matrix-left-inverse, and the entire statements of the existing determinant, adjugate and group-basis nodes.

## Not duplicates

No new nodes are delivered. In particular, I did not duplicate lem-trf-fg-torsionfree-group-free, lem-weil-pbc-cauchy-binet, lem-weil-pbc-matrix-adjugate-identity, def-weil-pbc-matrix-determinant, or def-weil-matrix. The existing Gordan lemma gives finiteness of cone lattice points, not a basis inside S, and was not used. The existing face-localization and sharpening nodes assume a face and do not directly apply to the image of a general chart; the explicit calculation in Step 2 avoids an unjustified citation of them.

## Review by Q10

I checked the statement against the actual ILO nodal chart, and distinguished its general algebraic refinement from that specific source example. There is no statement dispute: all original hypotheses and conclusions are retained. I checked the exact definition of fs and group completion in def-trf-fs-log-blowup; it supplies the integrality and saturation used here. I read the current chapter and unit records and the current blueprint locality proof, preserving the historical ancestry without changing any higher-level route. There are no new nodes whose hypotheses or literature attribution would need independent checking.

Step 1 uses def-trf-fs-log-blowup for the embedding in the group completion and finite monoid generation, and lem-trf-fg-torsionfree-group-free for a finite integer basis. Its statement explicitly assumes finite generation and torsion-freeness; the former is proved using images of the monoid generators and the latter is a hypothesis of the item. This basis is initially arbitrary, so the proof does not prematurely assume that it lies in Q or S.

Step 2 uses exactly the saturation clause of def-trf-fs-log-blowup. The lift x lies in Q^gp, the integer n is positive, a,b lie in P, and g(a),g(b) lie in Q. Thus n(x+g(b)) lies in Q and all hypotheses of that clause are checked. The image calculation is written in full, rather than cited as a quotient-saturation theorem.

Step 3 uses the full rectangular Cauchy–Binet statement and the determinant's defining formula. B has r rows and m columns and C has m rows and r columns; BC is the r by r identity. Thus this is precisely the statement of the cited node over the commutative ring Z, including its empty-sum convention when m<r. The determinant definition supplies det I=1. Step 4 only uses integer values of that formula and the elementary least-positive-integer principle, with nonemptiness already supplied by Step 3.

Step 5 uses the actual two-sided adjugate identity over Q; dividing by the nonzero determinant gives the asserted inverse and independence. No theorem about arbitrary fundamental domains is used. The integer y is chosen only under the proper-span assumption, z is integral by the defining floor inequalities, x=y-Az is integral, and a is rational with each coefficient in [0,1). Not-all-zero follows from y being outside the integer column span. This is the explicit elementary calculation following the cited adjugate identity.

Step 6 first applies the saturation proved in Step 2, with a positive common denominator and nonnegative integer coefficients; x belongs to the lattice, so saturation's ambient-group hypothesis holds. Its two cited nodes give the square Cauchy–Binet formula over Q and the precise determinant sum used to compute det E. The resulting replacement matrix has integer entries despite the rational intermediate E. The strict inequalities require a_j>0 and a_j<1; both came from Step 5. The contradiction is therefore against the same positive integer D minimized in Step 4, not a real-valued minimum. Steps 7 and 8 are elementary basis-coordinate and quotient-kernel calculations; every existence and uniqueness statement is written out.

Step 9 uses def-trf-fs-log-blowup solely for integrality and the group-completion generator relations. It explicitly checks that the formula lands in Q, that it restricts to g, that equality of h-values reduces to injectivity of Phi, and that group completion of P times N^r is P^gp times Z^r by its universal property. Thus the isomorphism proved for Phi is precisely h^gp rather than merely an unrelated splitting of the group extension.

For small cases I checked r=0 (including P=Q={0} and any g^gp isomorphism), P={0}, Q=N, non-sharp Q=Z, and groups with torsion units such as Q=N times Z/2 with P=Z/2 embedded as the units. The proof needs torsion-freeness only for L, not Q^gp. For a non-face image, P=N -> Q=N^2, 1 maps to (1,1), the quotient image S is Z, so the face lemmas cannot be applied directly but Step 2 works. For a non-unimodular tuple in the saturated monoid N^2, the columns (1,0),(1,2) have determinant 2 and the floor construction gives x=(1,1) with coefficients (1/2,1/2), reducing the determinant to 1. For r=1 and A=(-2), choosing y=1 gives a=1/2 and x=-1, so negative coordinates and determinant signs cause no problem. Without saturation, Q generated by 2 and 3 in Z, P={0}, would fail to contain either Z-basis vector 1 or -1; this confirms that the saturation hypothesis is doing necessary work.

Against delivery-errors B–E: there are no statement-only new nodes to check or duplicate; TeX is singly represented in the decoded strings; source tags were checked in the local tag map and tex; every non-elementary external input has an existing node whose statement I read and quote. Cauchy–Binet is declared as an off-unit generic tool in split_report.tool_uses because this unit has no matrix theorem supplying it. No dependency points back to this item, no clause is repackaged as a new node, and all intermediate algebraic comparisons are written explicitly. All nine proof steps are shorter than 1000 characters, so there is no >2000-character step hiding a lemma.

## What could not be finished

Nothing mathematical remains in this one-level split. Delivery validation and push are recorded below after the required tools finish.

## Delivery validation

The required `deliver.py Q10 lem-trf-fs-chart-free-factorization --no-push` exited 0 and printed `OK (not pushed)` at commit `8f64a76ac9`; server preflight passed. The delivery uses the direct-delivery worker's self-review above; the maintainer's independent review follows the push.
