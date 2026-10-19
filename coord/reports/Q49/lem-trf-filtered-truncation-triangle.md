# Stage-1 report: lem-trf-filtered-truncation-triangle

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-filtered-truncation-triangle.json`: existing statement node, now split into five sourced proof steps; no new child nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.
- `searches.jsonl`: Mathlib searches run for the item; all relevant hits were ordinary derived-category truncations or generic localization and did not match finite filtered localization.

## Attachments

None. Grep of both read-only source checkouts for the item id, filtered-derived terminology and truncation declarations found no sorry-free project declaration stating this item exactly.

## WANTED:

None. Varshavsky's trace-formula PDF supplies §§5.1.1–5.1.2. Stacks `derived.tex` Tags 05S1–05S6 supply the filtered localization and bounded-below truncation facts used to expand the proof.

## Not duplicates

- `lem-trf-filtered-truncation-triangle` vs `lem-trf-filtered-derived-hom-calculus`: the existing node assumes enough injectives and additionally constructs filtered RHom; this item assumes only an abelian category and proves the generic truncation/adjunction structure.
- `lem-trf-filtered-truncation-triangle` vs `def-trf-bounded-filtered-derived-category`: that definition is specialized to bounded constructible pro-etale sheaves and only records complex-level truncations; it does not state descent, universal Hom bijections, triangle uniqueness or the pure-grade equivalence.
- `lem-trf-filtered-truncation-triangle` vs `lem-trf-filtered-localization-injective-model`: the existing node assumes enough injectives and supplies injective representatives, not universal truncations for arbitrary abelian categories.
- `lem-trf-filtered-truncation-triangle` vs `lem-trf-filtered-cone-localization`: the latter supplies the general cone localization and triangulated structure; it does not identify the filtration truncation cone or prove its adjunctions.
- `lem-trf-filtered-truncation-triangle` vs `lem-trf-filtered-functor-graded-comparison`: that node concerns already supplied filtered lifts and their graded comparisons, and uses this item's universal truncations; it does not state the generic truncation theorem.

## What was wrong or incomplete

The imported source has an adjoint-label error. Varshavsky §5.1.1(c) prints the subcomplex truncation as left adjoint and the quotient truncation as right adjoint. The universal maps in the item have the opposite, correct directions: for high-supported `L`, maps `L -> M` factor uniquely through `t_{>=r}M`; for low-supported `R`, maps `M -> R` factor uniquely through `t_{<r}M`. Over `F_2` in degree zero, putting a one-dimensional vector space in grade 0 and another in grade 1 gives an immediate counterexample to the printed labels. The item statement already contains the corrected formulation, so no statement change was needed.

The proof uses `lem-weil-pbc-triangle-morphism-extension` from the proper-base-change unit as a generic pre-triangulated tool for uniqueness of the comparison of supported triangles. This is an off-unit tool use for the lead to record; the trace unit itself does not provide that abstract triangle-morphism lemma.

## What I could not finish

No mathematical work remains in this one-level split. The required server dry run is the remaining validation gate; this worker does not push or deliver.

## Review by Q49

I read the worker contract, `coord/brief-stage1.md`, `stages/1-dag.md`, the chapter record, the `sk-i-global-additivity` unit record, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B–E. I read the item source and the complete filtered-category discussion in Varshavsky §§5.1.1–5.1.2, pp.39–40, and checked Stacks `derived.tex` Tags 05S1–05S6. The source typo in §5.1.1(c) was tested on the two one-dimensional `F_2` examples described above; the item has the corrected right/left adjoint directions.

Step 1 uses the filtration and filtered-complex definitions for induced and quotient filtrations and the finite-filtration exactness node to pass from graded quasi-isomorphisms to ordinary quasi-isomorphisms after forgetting. The existing cone-localization node supplies the homotopy-category localization, cone triangles and exactness. I checked that both truncations preserve every finite filtration interval and that their associated graded formulas are identity or zero in the stated ranges.

Step 2 computes the cone of `F^rM -> M` grade by grade: below `r` it maps identically to the quotient grade, while at or above `r` it is the contractible cone of an identity and the quotient grade is zero. This gives the displayed distinguished triangle, its graded pieces and naturality.

Step 3 replaces derived-supported objects by their truncations, then performs the finite-filtration roof argument: maps and homotopies from a high-supported representative to a low-supported representative vanish, and an acyclic graded denominator is killed by descending induction through the finite filtration. This gives vanishing in every shift and the two natural Hom bijections, hence the two adjunctions. I checked the boundary cases `r` outside the finite support, zero complexes, nonsplit two-step filtrations, and bounded-below complexes with infinitely many cochain degrees but uniform filtration bounds.

Step 4 applies the cited generic triangle-morphism extension lemma with middle map `1_M`. The all-shifts vanishing from Step 3 gives uniqueness of the outer components; reversing the comparison shows they are inverse. This proves the canonical triangle is uniquely characterized and functorial.

Step 5 computes `T_p` by two truncations, verifies `omega T_p = gr^p` on complexes, and checks that placing a complex in filtration degree `p` is a quasi-inverse on the pure-grade subcategory. The argument uses derived vanishing, so acyclic off-grade pieces are included. Every cited node's statement was opened and quoted verbatim in `citations.json`; `proof_deps` is exactly the union of the step uses. All five proof steps are under 2000 characters, no new node is a restatement of the item, and no SGA source is used.

## Second reading by Q49

- Source and item statement: I reopened Varshavsky PDF §5.1.1(a)–(e), §5.1.2(a)–(c), pp.39–40, and Stacks derived.tex Tags 05S1–05S6 (labels cross-checked in tags/tags). The finite uniformly bounded filtration, bounded-below complexes, localization at graded quasi-isomorphisms, exact \(\omega\)/\(\operatorname{gr}^p\), truncation formulas, triangle, uniqueness, adjunctions, and pure-grade equivalence agree clause by clause. The printed left/right labels in §5.1.1(c) are reversed; the item retains the mathematically correct directions, with the existing \(\mathbf F_2\) degree-0/degree-1 test as a counterexample to the print.
- Step 1: checked the induced and quotient filtrations against `def-sp-filtration` and `def-sp-filtered-complex-subquotients`, the filtered exactness statement against `lem-trf-finite-filtered-graded-exactness`, and the finite induction through the long cohomology sequence against `lem-weil-pbc-complex-ses-homology-long-exact`; checked descent and cone exactness against `lem-trf-filtered-cone-localization`. Verdict: correct; I made the short-exact-sequence and cohomology induction explicit and added the long-exact citation.
- Step 2: checked the grade-by-grade cone calculation against Varshavsky §5.1.2(c) and the cone-localization statement. For \(p<r\) the cone maps identically to the quotient grade, and for \(p\ge r\) it is the cone of an identity; naturality follows on chain maps. Verdict: correct, unchanged.
- Step 3: checked the supported replacements, orthogonality, and both Hom factorizations against Varshavsky §5.1.1(c), §5.1.2(b)–(c), Stacks 05S1–05S2, and the localization statement. The finite-filtration denominator refinement via \(t_{\ge r}Z\) makes the roof argument valid without enough injectives. Verdict: correct after repair; I replaced “the same roof argument” with the explicit denominator, factorization, and uniqueness argument.
- Step 4: checked the triangle comparison against `lem-weil-pbc-triangle-morphism-extension`, including the hypothesis \(\operatorname{Hom}(L[1],t_{<r}M)=0\), and checked the reverse comparison and identity composites. Verdict: correct, unchanged.
- Step 5: checked the two truncations defining \(T_p\), the canonical underlying identification, and the pure-grade quasi-inverse against Varshavsky §5.1.1(d)–(e) and §5.1.2(b), including acyclic off-grade pieces. Verdict: correct, unchanged.
- New nodes: none were created in this split, so B1–B7 and duplicate/Mathlib-leaf checks are vacuous. I rechecked the existing dependency statements and the recorded Mathlib searches; the item has no matching Mathlib declaration.
- Changes made: repaired Step 1's hidden cohomology induction, added its exact citation and dependency, and expanded Step 3's roof refinement and Hom-bijection proof. Preserved the worker's source-error note, five-step structure, citations, and report sections.
