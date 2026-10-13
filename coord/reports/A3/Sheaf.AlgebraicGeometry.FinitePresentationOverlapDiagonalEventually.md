## What changed

Completed the body of
`AlgebraicGeometry.finitePresentation_overlap_diagonal_eventually` without changing its
signature, visibility, or existing docstring. Added four proved private helpers:
`conjugate_eq_id`, `diagonal_pull_iff`, `pullback_map_zero_of_comp`, and `refinement_comp`.
The proof transfers finite presentation through the component isomorphism, forms the
identity defect, derives its limit vanishing from limit coherence, obtains a single
finite stage of vanishing, proves persistence by composition of the canonical chart
refinements, and converts the vanishing back to the required transition identity.

Added the module
`Sheaf.AlgebraicGeometry.FinitePresentationChartMapZeroEventually`, stating the geometric
comparison step for an arbitrary module map on a base-changed affine chart. It concludes
vanishing at just one stage. It contains no overlap transition system, component model,
coherence assumption, diagonal equation, or persistence conclusion. Its docstring and
node give the argument through the existing zero-map descent theorem and canonical
pullback comparisons, including the native/tensor pullback comparison by adjoint
uniqueness.

The item's proof imports the new chart module and the proved upstream
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`; its former direct proof import
of `FinitePresentationZeroMapDescent` is now needed by the chart module. All original
public imports remain. Both node proof records now describe this route. No existing
interface or definition was changed. A declaration-local unused-variable linter option
preserves the original unused existential binder `hkl` and the redundant explicit
quasi-coherence hypothesis, without renaming any binder.

## Proved and sorry left

Closed the item's only direct hole:
`AlgebraicGeometry.finitePresentation_overlap_diagonal_eventually`
(node `lem-pc-fp-overlap-diagonal-eventually`). All four private helpers are completely
proved, and there are no remaining direct sorries in the item's module.

Added one hole:
`AlgebraicGeometry.finitePresentation_chart_map_zero_eventually`
(node `lem-pc-fp-chart-map-zero-eventually`), whose entire proof is `by sorry` in its
own new module. Thus this is a decomposition, with one upper hole closed and one
strictly partial geometric step split off, net zero holes. It is not an axiom-free
completion of the whole dependency closure. The existing
`finitePresentation_zero_map_descent` declaration is retained as the planned input
to that geometric step.

Both sandbox modules compiled together in import order with lcompile.py, without
errors or warnings. The new statement was checked on zero modules, empty affine
charts, singleton directed preorders, and a constant diagram: zero-map descent and
canonical pullback isomorphisms apply in each case. No nonempty cover or index-set
hypothesis was added; the given chart and stage already provide the needed indices.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent` from the item's module,
replacing it with the single-stage chart lemma. The zero-map descent module remains
imported by the new chart module and is still needed in the argument; it is not
pruned from the targets' import closure. No planned node or module is pruned.
The original node's direct zero-map proof dependency is now routed through
`lem-pc-fp-chart-map-zero-eventually`. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report described a theorem with materially the full eventual
identity statement under a new name. That proposed reduction was invalid. Its report
has been replaced; no old stage theorem or node is included in this delivery.

The original DAG's zero-map descent step suppresses two comparisons: the chart tower
versus base change of its structural map to Spec(R_k), and tensor versus native module
pullback. The new node states precisely the geometric step remaining after those
comparisons. All overlap naturality, conjugation, and persistence glue is actually
proved in the item's module, rather than placed in that new hole. The supplied
quasi-coherence assumptions are redundant because finite presentation already gives
quasi-coherence, but the original signature is preserved exactly.

Searches used msearch LeanFinder, Loogle, grep, and LeanSearch. LeanSearch returned
Internal Server Error and is recorded as unavailable. LeanFinder found structure-sheaf
section vanishing on affine limits, not arbitrary module-map vanishing on the prescribed
chart. Repository search located and reused the finite-presentation pullback and
isomorphism results in the proved upstream FiniteDescent module. Blueprint search
found no duplicate chart-map statement. The source clause was read at Stacks Tag 01ZR.

## New nodes

`lem-pc-fp-chart-map-zero-eventually` records
`AlgebraicGeometry.finitePresentation_chart_map_zero_eventually` in
`lean/Sheaf/AlgebraicGeometry/FinitePresentationChartMapZeroEventually.lean`.
It isolates the comparison needed to apply the existing zero-map descent theorem on
a single affine chart. It is strictly a part of the original argument: it accepts an
arbitrary map with a limit-zero hypothesis and supplies one stage of zero, leaving
both the production of that hypothesis and the transition/persistence conclusions
to the proved parent. Its module and node carry the source, complete proof in words,
three kinds of Mathlib search, and the original chapter and unit. No change record is
needed because no existing signature, visibility, or definition was changed.

## Second reading by A3

1. I compared the delivered overlap module with the repository version. The existing theorem
signature, hypotheses, conclusion, visibility, and docstring are unchanged byte for byte;
only proof helpers and proof imports changed. The new chart theorem has its own module and
node, with its signature matching the recorded node. Verdict: pass.

2. I compiled both sandbox modules together with `lcompile.py --all`; they compile without
errors or warnings. The overlap theorem has no direct `sorry`; the only added `sorry` is the
named chart theorem, with a docstring and matching node. The proof uses no forbidden
constructs. Axiom probing is delegated to the delivery dry run. Verdict: pass pending the
same dry-run probe.

3. The chart theorem is a strict one-stage geometric reduction: it takes one arbitrary map
and a limit-zero equation and returns one finite stage of vanishing. It does not restate the
overlap theorem, and it leaves transition coherence and persistence in the parent proof. Its
hypotheses include the finite-type/quasi-coherent source and finite-presentation/
quasi-coherent target required by zero-map descent; no cover nonemptiness assumption is
introduced. I checked zero modules, empty charts, singleton directed systems, and constant
diagrams as edge cases. Searches recorded in `searches.jsonl` found no existing declaration
of this statement. Verdict: pass.

4. The overlap proof follows the unit route: transfer finite presentation to the component,
form the identity defect, use coherence for limit vanishing, apply the one-stage chart
reduction, and prove persistence by composition of canonical refinements. The private helper
`refinement_comp` proves the pullback-map composition directly. The unit record has no realized
entries to alter, so no route entry was bypassed. Verdict: pass.

5. I checked that the old direct proof import in the overlap module was replaced with the
chart reduction import; the zero-map descent module remains transitively required by the new
chart module. The item and chart node proof/proof-dependency records agree with the imports
and declarations. No existing definition or statement was changed. Verdict: pass.

I changed only this report section during second reading; no Lean statement or proof was
altered. I independently read [Stacks Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR),
including its affine-case reduction in the first proof. Its clause (3) is stated for finitely
presented source and target; the finite-type-source extension used here is supplied by the
existing `finitePresentation_zero_map_descent` statement and its generator argument. I read
that declaration, `BaseChangeConventions.moduleBaseChange`, and
`TensorPullback.nonempty_tensorPullbackAdjunction`: the claimed native/tensor comparison
really follows from uniqueness of left adjoints to the same pushforward. The chart is affine
because the stage map is a base change of a map of spectra, so its structural morphism to
Spec(R_k) is quasi-compact even without quasi-compactness assumptions on the original f.
My independent LeanFinder search for finite-type morphism vanishing after extension to a
filtered colimit found only elementwise module-colimit criteria and unrelated results,
not a direct substitute for the chart comparison. Repository searches also found only the
existing zero-map and section-vanishing models already used by this reduction.
