## What changed

Replaced the hole in `AlgebraicGeometry.Etale.graph_proper_support_unit` with a
reduction to the proper-first path in one compactification. Its statement is unchanged.
Only this existing Lean module and its own DAG node are changed. Added the modules
`Sheaf.AlgebraicGeometry.EtaleGraphProperPrecompositionUnit` and
`Sheaf.AlgebraicGeometry.EtaleGraphCompactificationUnit`, with their nodes. The latter
contains a complete proof of the homotopy normalization of the inverse graph comparison.
After local model wrappers and named lemmas improved type checking, that self-contained
calculation was separated to meet the per-file compile limit.

Take the chosen compactification c of b and its proper postcomposition c.postcomp p.
The proof constructs tau by composing theta with the sheaf graph map and the ordinary
proper direct-image compositor. It proves tau's support normalization from htheta,
graph sheaf normalization, naturality and associativity of direct-image composition.

The etale-first side is proved completely: the existing proper postcomposition theorem
identifies its compactification word; a private abstract lemma computes its right-derived
unit using naturality, the defining graph-derived formula and the canonical proper
composition unit. The two sides then agree after an explicitly invertible postcomposition,
which is cancelled. All of these calculations are Lean proofs in the item. The calculation is stated in a
private helper with an abstract compactification and its equality to the chosen one;
the public theorem specializes it. This avoids expanding the chosen compactification
throughout the long unit calculation.

The remaining theorem concerns only q proper, v etale, and one compactification of qv.
It has no second etale/proper factorization. In particular the arbitrary etale source leg
b of the original square is replaced by the open immersion of that single compactification.
The original theorem is not an immediate application or a renaming of the new theorem:
its etale-first word and its unit are identified by the calculations above.

Validation: `lcompile.py --all` compiled all three delivered Lean modules successfully.
The original theorem signature is byte-for-byte unchanged; all DAG dependency IDs resolve,
and the files contain no profiler settings or lines longer than 100 characters.

## Proved and sorry left

This is a decomposition, not a net reduction in holes: one original hole closed and one
strictly simpler geometric hole added. There were 1 original holes; 0 are closed without
an added obligation, and 1 is reduced.

Closed in the item:
`AlgebraicGeometry.Etale.graph_proper_support_unit`
(node `lem-pur-graph-proper-support-unit`). The private lemmas `comp_homotopy_inv`,
`exact_left_unit_app`, `proper_comp_unit`, `postcomposition_unit`,
`cancel_whisker_iso`, `postcomp_sheaf_normalization`, `postcomp_word`, and
`post_model_app` and
`graph_proper_support_unit_aux` have complete proofs. The public theorem
`AlgebraicGeometry.Etale.graph_compactification_unit` is also proved, in its own module
(node `lem-pur-graph-compactification-unit`). The private `post_word` and
`post_model` definitions are explicit compositions of existing isomorphisms, with no holes;
the model is kept irreducible during the final unit calculation.

The only sorry left in the delivery is
`AlgebraicGeometry.Etale.graph_proper_precomposition_unit`
(node `lem-pur-graph-proper-precomposition-unit`). Its entire proof is `by sorry`,
and its docstring and node specify the source, injective-model calculation and extension
to arbitrary homotopy objects. No definition or private declaration contains a hole.

## No longer needed

No original import is removed and no module is withdrawn. No global pruning is claimed.
The item directly uses the existing proper postcomposition result instead of repeating
the full four-arrow support argument. Its former direct proof dependencies
`lem-cbc-proper-support-sheaf-composition`,
`lem-asd-compact-support-graph-coherence`, and
`def-weil-compactifications-refinements` remain in the new proper-first obligation,
so they are not claimed to be globally unnecessary.

No import of `EtaleSupportExchangeRightMate` is needed: choosing c to be the already
chosen compactification makes expansion of the chosen graph comparison definitional.
No new refinement-coherence dependency is introduced by the etale-first calculation.
The exact compactification tower theorem is not used, since its exactness requirement
on the first sheaf functor does not apply to a general proper q_*.

## Where the brief, the DAG or earlier work was wrong

The named dependencies supply sheaf support composition, graph normalization and tower
coherence, but they do not directly state a unit comparison for proper-first composition
with the possibly nonexact sheaf functor q_*. The existing
`exactCompactificationUnit_tower` requires both input functors to be exact. Treating q_*
as exact would be incorrect. This delivery isolates only that proper-first calculation;
it proves the other half and the pasting instead of leaving the original square under
another name. No target or existing auxiliary statement is changed or disputed.

## New nodes

`lem-pur-graph-proper-precomposition-unit`, in
`dag/nodes/sec-smooth-purity/lem-pur-graph-proper-precomposition-unit.json`, records the
proper-first unit normalization against one compactification. Its Lean declaration is
`AlgebraicGeometry.Etale.graph_proper_precomposition_unit` in the new module. Its source
is the construction in the first paragraph of Stacks Tag 0F7B, transported by Tags 0F7I
and 0F7J. Identity proper maps, empty schemes and zero coefficients require no additional
hypotheses. The fixed blueprint unit route is unchanged. No change record is needed:
no existing public interface was altered.

`lem-pur-graph-compactification-unit`, in
`dag/nodes/sec-smooth-purity/lem-pur-graph-compactification-unit.json`, records the proved
homotopy formula for the inverse graph comparison. Its declaration is
`AlgebraicGeometry.Etale.graph_compactification_unit` in
`Sheaf.AlgebraicGeometry.EtaleGraphCompactificationUnit`. The proof unfolds the explicit
graph comparison and applies its existing component formula, then expands the exact-left
composite unit. This node adds no sorry. Its source is the existing graph construction
of SGA 4 XVII 6.2.11 and Stacks Tag 0F4L.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
