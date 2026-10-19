# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-chart-coordinate-nonzerodivisors.json` — repaired item, split statement; zero new nodes and zero Mathlib leaves.
- `citations.json` — six verbatim statement quotes, one for each of the three cited nodes in each proof step.

## Attachments

None. The project-source search for the item id, chart-coordinate terminology, and coordinate/nonzerodivisor combinations found no declaration stating the item. I read `WeilConjectures/Blowup/Affine/Principalization.lean`, including `AlgebraicGeometry.AffineBlowup.isRegular_awayAlgebraMap` and its standard-chart specialization: these prove injectivity on an unquotiented chart, not either quotient assertion of the item. They belong to the existing chart-generator node, not an attachment of this item.

## WANTED

None.

## What I checked and changed

I continued the retained split, citations and report, and read all five retained `searches.jsonl` results. The returned delivery is identified in the independent review as `9cce3d3efd594dc07c02e5fc91e2d28fe74fb7be`; the retained proof and report exhibit precisely the simultaneous-quotient error described there. Compared with the current shared item, its statement, statement dependencies, source, chapter, unit and creation metadata are unchanged. The current shared item is unsplit. The delivery tool rebases the repaired split fields onto current main and preserves current maintainer fields. The required initial dry run of the retained split exited successfully at `934879d612`; that mechanical success does not address the mathematical return.

The item source is ILO, *Travaux de Gabber*, Exposé VIII, Lemma 4.2.9 and its proof, printed p. 121 (PDF p. 127). I read its local parameter and chart computation. The split expands the nonzerodivisor check needed for the individual strict-transform closures in Step 4 of `lem-trf-permissible-coordinate-chart`. I also read Stacks Tag 00NQ, `algebra.tex`, label `lemma-regular-ring-CM`, and Tag 0BIQ, `more-algebra.tex`, label `lemma-blowup-regular-sequence`, including its proof. The former gives regular sequences for minimal maximal-ideal generators and regular initial quotients; the latter supplies the displayed chart presentation for a regular sequence. I read the chart-generator blueprint statement and proof: a chart is a subalgebra of the localization in which its generator is invertible.

The statement is correct and has not been changed. No statement dispute is needed: the fault was in the earlier proof, not in the imported assertion. Its first clause concerns each individual quotient `A_j/(u_i)`, not the quotient by all the chart coordinates.

## Repair of the returned findings

1. **E4/E3, wrong quotient and missing first clause.** Step 1 now fixes one `i` and sets `H=J\{j,i}` and `B=R/(t_i)`. The relation indexed by `i` becomes `t_i=0`; every variable `u_h` for `h in H` survives. The proof explicitly identifies `A_j/(u_i)` with `B[u_h : h in H]/(bar(t_h)-bar(t_j)u_h)` by coefficient and variable maps in both directions. The permutation beginning `t_i,t_j,(t_h)` gives a regular sequence over `B` beginning with `bar(t_j)`. The existing presentation theorem identifies this quotient as `B[I_i/bar(t_j)]`, for `I_i=(bar(t_j),bar(t_h) : h in H)`. The existing chart-generator theorem then gives exactly the desired injectivity. Step 1 now cites all three supporting nodes, and citations.json has the two additional quotes it needs. The report and split_report no longer claim that the simultaneous-coordinate quotient suffices.
2. **Valid outside-parameter argument retained and checked.** Step 2 still fixes `k notin J` and computes the quotient over `R/(t_k)`. I made the ideal, surviving variables and correspondence of the multiplication maps explicit. Regularity follows from the permutation beginning `t_k,t_j,(t_h : h in J\{j})`, and the same chart-presentation and chart-generator statements apply. Neither step assumes that arbitrary blowups commute with a nonflat quotient; each uses the explicit regular-sequence presentation.
3. **Edge-case correction in the report.** For `J={j}` the first assertion is vacuous. It is not an extra assertion about quotienting by an empty list. For `|J|=2` Step 1 has no surviving variable, and its singleton chart is the base `R/(t_i)`. For `|J|>=3` the surviving variables remain present. If `J` is the full parameter set, Step 2 is vacuous. If `d=0`, no nonempty `J` exists.

The concrete three-parameter check uses `R=k[x,y,z]_(x,y,z)`, `J={1,2,3}`, `j=1`: `A=R[u,v]/(y-xu,z-xv)`. The required quotient by `u` is `(R/(y))[v]/(z-xv)`, not `R/(y,z)`. Step 1 now preserves `v` and identifies the former as the `x`-chart of `(x,z)` over `R/(y)`. This explicitly distinguishes the object that the earlier proof missed. The review's counterexample `k[a,v]/(av)` also shows why injectivity modulo `v` cannot be lifted without an argument.

## Existing tools, searches and route

No new node was created. The existing regular-parameter, regular-sequence chart-presentation and chart-generator nodes supply all non-elementary facts. DAG searches by Tags 00NQ and 0BIQ and coordinate-quotient terminology, and blueprint searches for chart coordinates, nonzerodivisors and blowups, found these tools rather than a noncircular replacement for the item. The parent chart theorem depends on this item and cannot be used to prove it. The item retains its nearest blueprint ancestor and `same_as: []`.

The five logged searches are reused because the statement and search question did not change. Their actual hits concern regular-sequence tails/localizations, power series nonzerodivisors, affine covers and unrelated coordinate constructions, not the blowup-coordinate assertion. The Loogle result was an unknown-identifier response, not affirmative evidence of absence. No new Mathlib match or search is asserted in this repair. The existing metadata spelling of the grep query includes its directory; the preserved log records its original pattern and `AlgebraicGeometry` subdirectory separately.

The generic regular-local and chart-generator tools remain declared in `split_report.tool_uses`, with the latter updated to explain its use in both steps. I read the chapter and unit records and kept the historical algebraic branch and coordinate-chart route. No target statement, coefficient category, comparison morphism, unit binding or higher-level route changes. No SGA source is cited. No Lean was written and no compiler, Lake, build, local DAG checker or local split-review tool was run.

## What I could not finish

Nothing mathematical remains open in this one-level split. Final server dry run and push are performed after this report is written.

## Review by NB

I reread the complete maintainer `review.md`, the item and its parent, the three cited node statements, the regular-local/parameter/regular-sequence/chart definitions, ILO VIII Lemma 4.2.9, Stacks 00NQ and 0BIQ, and the chart-generator blueprint proof with the repaired node open. There are no new node statements to check against B1–B9.

In Step 1, `lem-weil-pbc-regular-local-generators-regular-sequence` supplies regularity after the specified parameter permutation. The definition of a regular sequence gives its tail over `R/(t_i)` and its initial segment; the final quotient remains nonzero since these parameters lie in the original maximal ideal. `lem-trf-blowup-chart-regular-sequence-presentation` states precisely the canonical polynomial quotient and the variable-to-fraction correspondence used for that remaining sequence. `lemma-nagata-chart-generator-regular` states injectivity of the generator on this identified chart. Its membership hypothesis is satisfied because `bar(t_j)` is explicitly a generator of `I_i`. The elementary part is the quotient presentation, whose two maps are written out. The distinct indices `i!=j` and the removal of `i` from `H` ensure that no variable or parameter is inadvertently killed twice. This is the substantive correction requested by the return.

In Step 2, the same regular-parameter statement supplies the sequence with `t_k` first. Here `k notin J` ensures that all chart parameters survive as the required distinct tail entries. The chart-presentation statement applies to exactly that tail's initial segment over `R/(t_k)`; its coefficient correspondence takes the image of `t_j` to the chart generator. The chart-generator statement then gives the exact multiplication map in the conclusion, since `bar(t_j) in I_k`. This uses only the statement of each cited node, not an internal construction from its proof. The elementary quotient calculation does not use a general base-change theorem.

I checked the singleton-center and two-/three-parameter cases above, the full-center and dimension-zero vacuous cases, and that every parameter lies in the maximal ideal. No excellence, domain theorem, invertibility assumption or characteristic restriction is introduced. Every non-elementary inference in the two steps is supported by one of the three cited statements; no child restates a clause of the item. Both steps are below 2000 characters (1377 and 1182), and their remaining quotient identifications are direct universal-property calculations, not hidden lemmas. All six citation quotes are literal substrings of the corresponding node statements, and proof_deps is exactly the union of uses. The returned statement and source remain intact; the report now describes individual quotients and the correct vacuous case.
