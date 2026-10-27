## What changed

Filled the proof body of `CategoryTheory.stack_chartwise_comp` in
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`, without changing any
existing signature, definition, attribute, or public import. Added private proof
imports of `StackCompositeChartRefinement` and `SchemeEtaleSourceTargetProperties`.

For each scheme test of the composite, its geometric refinement supplies compatible
charts of the two factors. The existing test hypotheses give the two scheme-map
properties. The proof checks all five scheme composition instances explicitly,
uses the equality of projections, and applies pointwise étale locality with the
identity target chart. It finally forgets the chart-property clause to recover
representability. Both the empty-chart case and nonsurjective charts are included.

The geometric refinement is isolated in one new module and DAG node. It contains
no horizontal morphism property: its remaining task is the construction of the
iterated representing space and compatible charts, independent of smoothness,
étaleness, flatness, or either finiteness property. Its docstring and node describe
this construction from Tags 0300, 045B and 03MJ. Updated the parent composition
proof steps and proof dependencies to match this argument.

## Proved and sorry left

Original item: 4 direct holes. Closed the direct hole in
`CategoryTheory.stack_chartwise_comp` by a complete Lean proof from the geometric
refinement and the existing scheme-locality theorem. This is a **decomposition**,
not a net proof closure: one original hole is replaced by one strictly geometric
hole. Holes added: 1. Net direct hole reduction: 0.

The three original holes still in the item, each attached to
`lem-sfb-stack-chartwise-smooth-etale-calculus`, are:

- `CategoryTheory.stack_chartwise_openCover`;
- `CategoryTheory.surjective_moduli_iff_chartwise`;
- `CategoryTheory.etale_moduli_scheme_coproduct`.

The new hole is `CategoryTheory.stack_composite_chart_refinement`, attached to
`lem-sfb-stack-composite-chart-refinement`. It is a public named theorem with
exactly `by sorry` as its proof. There are no new definition holes.

Validation: `lcompile.py --all` compiled both delivered modules in import order;
`StackCompositeChartRefinement` took 33.9 s and the item took 41.9 s, both below
the 60-second limit. The compile was clean.

The already complete base-change, implications, and two field-lifting permanence
proofs are preserved. No source-library declaration is changed.

## No longer needed

No existing imports were removed, and no module is withdrawn or claimed globally
pruned. The composition argument no longer passes through a separate abstract
space-property composition theorem or replacement of scheme tests by all space
tests (old parent steps 5 and 6). It works directly with compatible scheme charts
and pointwise scheme locality. The algebraic-space presentation criterion remains
in the parent's dependencies for its untouched open-cover argument; fibre-product
and representable-pullback facts remain needed by the geometric refinement. These
nodes are therefore not globally pruned.

## Where the brief, the DAG or earlier work was wrong

The dependency declarations provide algebraic-space pullback existence and scheme
locality, but do not supply the compatible charts and projection comparisons needed
for the composite stack test. The new lemma makes precisely that missing geometry
explicit. The schemes in that refinement must be allowed to depend on a point of
the source chart and on any chosen presentation of the f-test. Fixing an arbitrary
presentation in advance without this compatibility would not justify applying the
two ModuliSpaceTest hypotheses.

Searches of Mathlib, WeilConjectures, Sheaf, the DAG, and the current blueprint found
no existing declaration of this compatible-chart assertion. LeanSearch and
LeanFinder returned scheme composition/permanence and stalk functoriality results;
the dedicated grep returned no match. The three searches are recorded verbatim in
the new node and in searches.jsonl. The supplied unit record has no realized
statement or proof-step nodes, and the current blueprint unit was read; no unit or
chapter route is changed.

Edge cases checked mathematically: an empty chart gives no pointwise obligation;
an empty target or test is permitted; neither individual source chart is required
to be surjective; only the auxiliary atlas W of B is chosen surjective; no
Noetherian, quasi-compactness, or finiteness hypothesis is used. The construction
works for categories fibred in groupoids and does not need a stack atlas.

## New nodes

`lem-sfb-stack-composite-chart-refinement`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-stack-composite-chart-refinement.json`,
with module `Sheaf.AlgebraicGeometry.StackCompositeChartRefinement` and declaration
`CategoryTheory.stack_composite_chart_refinement`: the property-independent
iterated-test representation and pointwise compatible-chart construction from
parent steps 3 and 7. Its three proof steps spell out representing the iterated
pullback, lifting a point through an étale atlas, and comparison with any chosen
f-test presentation. No change record is needed: existing interfaces are unchanged.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
