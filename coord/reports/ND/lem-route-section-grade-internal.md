# Stage-1 report: lem-route-section-grade-internal

## Files written

- `dag/nodes/sec-nagata-compactification/lem-route-section-grade-internal.json`: corrected item, split proof, and searches.
- `dag/nodes/sec-nagata-compactification/lem-route-qcoherent-direct-summand.json`: statement-only supporting lemma; no Mathlib exact match.
- `dag/nodes/sec-nagata-compactification/lem-route-range-internal-of-bijective-sum.json`: statement-only additive range lemma; Mathlib provides only the more general `DirectSum.Decomposition` APIs.
- `citations.json`: verbatim statement quotes for every cited step.

## Attachments

No finished declaration was found. The live source declaration `AlgebraicGeometry.RelativeProjAlgebra.sectionGrade_internal` still has `sorry` in `lean/Sheaf/AlgebraicGeometry/RelativeProjData.lean:92`.

## WANTED

None.

## Not duplicates

- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-quasi-coherent-module-kernel`: the existing node states quasi-coherence of the kernel of a morphism; the new node states the retract/direct-summand consequence for a module split by maps `i,p`.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-affine-algebra-module-kernel`: the existing node treats kernels of maps from free algebra modules; the new node states quasi-coherence of an arbitrary split retract.
- `lem-route-qcoherent-direct-summand` vs `lem-pc-affine-ideal-intersection-inclusion`: the existing node is an affine ideal-intersection inclusion for two quasi-coherent modules; the new node is the general retract criterion for one module.
- `lem-route-qcoherent-direct-summand` vs `lem-pc-ideal-data-recursive-power-comparison`: the existing node compares recursive ideal powers with ideal-sheaf data; the new node concerns quasi-coherence of a retract.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-affine-completion-baseChange-unit`: the existing node is a completion base-change isomorphism for affine modules; the new node is a retract criterion.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-affine-formal-quotient-comparison`: the existing node identifies formal quotients on an affine scheme; the new node concerns direct summands of quasi-coherent modules.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-affine-intersection-quotients-stalk`: the existing node constructs stalkwise quotient filtrations; the new node is a module retract quasi-coherence statement.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-affine-map-annihilation-sheafification`: the existing node transfers annihilation through tilde and sheafification; the new node concerns retracts.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-affine-pushforward-free-evaluation`: the existing node characterizes epimorphisms from finite free pushforwards on affines; the new node gives quasi-coherence of a split summand.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-artin-rees-affine-comparison`: the existing node is an Artin–Rees section-intersection comparison; the new node is the direct-summand closure property.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-formal-associated-graded-affine-multiplication`: the existing node constructs affine multiplication on associated-graded pieces; the new node concerns retracts of quasi-coherent modules.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-formal-associated-graded-multiplication`: the existing node constructs multiplication maps for associated-graded ideal pieces; the new node is a retract criterion.
- `lem-route-qcoherent-direct-summand` vs `lem-weil-pbc-formal-associated-graded-polynomial-cover`: the existing node gives a local polynomial cover of graded ideal pieces; the new node concerns quasi-coherent direct summands.
- `lem-route-range-internal-of-bijective-sum` vs `lem-weil-pbc-quasi-coherent-module-coproduct-closure`: the existing node concerns quasi-coherence of categorical coproducts; the new node concerns injective additive maps and internal ranges in an ambient group.
- `lem-route-range-internal-of-bijective-sum` vs `lem-weil-pbc-quasi-coherent-module-direct-sum`: the existing node proves quasi-coherence of a binary direct sum of sheaves; the new node proves internality of ranges of an arbitrary indexed family of additive maps whose sum map is bijective.

## Review by ND

I read the live item, `RelativeProjData.lean`, the parent `lem-nagata-proj-affine-restriction`, and the current blueprint ancestry. The original machine-made statement omitted the `RelativeProjAlgebra` data and claimed piecewise quasi-coherence without introducing the pieces; I replaced it with a self-contained statement that defines the section subgroups as ranges of the coproduct injections followed by `decomposition.hom`. For step 1 I checked the explicit injection/projection maps from the decomposition isomorphism and cited the new retract lemma, whose statement exactly supplies the quasi-coherence conclusion. For step 2 I checked the affine tilde/global-sections node: its counit isomorphism for quasi-coherent modules and preservation of all small colimits give the section-level direct-sum bijection; the tilde-sections node supplies the affine module model and quasi-coherence. For step 3 I checked the component maps are composites of coproduct injections and an isomorphism, hence injective, and cited the new range lemma verbatim for passage from the bijective sum map to `DirectSum.IsInternal` of the ranges. I searched the DAG and blueprint for both supporting statements and found no exact duplicates; the Mathlib searches found only generic `DirectSum.IsInternal`, `DirectSum.Decomposition.isInternal`, and `ofAddHom` APIs, with no RelativeProj or retract theorem. I checked edge cases conceptually: a one-degree family gives the whole section module, a zero piece gives the zero subgroup, and an empty affine scheme yields the zero module and the same internal-sum formulation.

## Source error

The provisional imported prose was not self-contained: it referred to “the quasi-coherent underlying module” and “every piece” without stating the `RelativeProjAlgebra` fields or the range definition of `sectionGrade`. This was corrected against the actual Lean structure and declaration.

## What remains

The two supporting lemmas are intentionally statement-only stage-1 nodes; their proofs belong to later stages.
