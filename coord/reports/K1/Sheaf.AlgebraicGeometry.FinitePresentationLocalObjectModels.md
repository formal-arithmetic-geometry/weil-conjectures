## What changed

Proved `AlgebraicGeometry.exists_finitePresentation_local_object_models` without changing
its signature or public imports. The proof chooses `Xi.affineCover.finiteSubcover`,
obtains a model for each fixed chart, bounds the finitely many model stages together
with `i`, and pulls that cover to the common stage.

The proved private helper `transport_chart_model` constructs the two chart transition
maps by `pullback.map` and `pullback.lift`. Its two projection equations let
`pullbackComp`, `pullbackCongr`, and the pullback of the existing component isomorphism
identify the new component with the restriction of `M`. Pullback preserves finite
presentation and quasi-coherence, so no new hole remains in this transport argument.
This helper does not require an isomorphism between the two limit charts.

Added `Sheaf.AlgebraicGeometry.FinitePresentationAffineChartModels`, containing only the
single-chart existence step, and its node. Added proof-only imports of that module,
`Mathlib.Data.Finset.Order`, `Mathlib.AlgebraicGeometry.Morphisms.Affine`, and
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`. Updated the item's proof route.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_finitePresentation_local_object_models`
(node `lem-pc-fp-local-object-models`). Its proof is complete Lean combining a new,
strictly smaller affine-chart statement with the finite-cover and transport arguments.

Added one hole:
`AlgebraicGeometry.exists_finitePresentation_affine_chart_object_models`
(node `lem-pc-fp-affine-chart-object-models`). It asks for a model at just one stage
on one prescribed affine chart, without any finite-cover or common-stage conclusion.
Its remaining work is the coordinate-ring colimit and associated-module comparison.
This is a decomposition, not a net reduction of the target-closure hole count.
There are no sorries left in the item's module or in its private helper.

## No longer needed

Removed the item's direct proof-only import of `Sheaf.Algebra.FinitePresentationColimit`;
it is now the proof dependency of the new single-chart module. It remains needed
transitively, so it and its node are not pruned. No other existing import, node or
module is pruned. The new lemma has no Noetherian, local finite-presentation,
quasi-compactness, or quasi-separatedness hypothesis on the ambient scheme morphism;
those assumptions are not needed for the single affine chart step.

## Where the brief, the DAG or earlier work was wrong

The original node's first step bundles algebraic module descent with the substantial
scheme/chart coordinate-ring dictionary; its only stated dependency provides the
algebraic clause. The new lemma isolates precisely that missing single-chart step.
The later-stage transport, previously hidden in prose, is now proved rather than
included in the new hole. No statement correction or forced adaptation was needed.

The local literature checkout does not contain `literature/stacks-project/limits.tex`.
I read the official Stacks pages for Tags 01ZR and 05N7. Searches used the prescribed
leanfinder, loogle, grep, and leansearch interfaces plus local source searches;
LeanSearch returned an internal server error, recorded as unavailable. The blueprint
searches for “affine module descent” and “05N7” returned no existing blueprint node.

Edge cases: the finite-subcover argument also works for empty Xi (an empty index family),
and the bounding finite set still contains i. No nonempty chart-index assumption is
used. The chart helper allows zero modules, empty charts, zero rings, a singleton
system, and a directed preorder rather than requiring antisymmetry. Its two triangle
identities come from the cone equation and the ring functor's composition equation.
The blueprint unit's `realized` arrays are empty; no unit statement or step is bypassed.

## New nodes

`lem-pc-fp-affine-chart-object-models` states the single affine chart existence clause
of the first proof of Stacks Tag 01ZR, reduced to the object clause of Tag 05N7.
Its module has one named public theorem with `:= by sorry` and a construction proof
in its docstring. Its DAG statement agrees with the Lean: arbitrary directed preorder,
ring diagram, affine limit, fixed i and morphism, finitely presented quasi-coherent M,
and a chosen affine chart. It asserts neither a finite cover nor later-stage models.
No change record is required because all existing signatures and visibility are preserved.

## Second reading by K1

1. Compared both delivered modules with the repository versions. The existing local-model
   theorem signature is byte-for-byte unchanged; the added affine-chart theorem is a new
   declaration recorded by its node. Verdict: pass.
2. Compiled both modules with `lcompile.py`; compilation succeeds with no errors. The local
   target has no `sorry`, and the only remaining `sorry` is the named affine-chart theorem.
   No forbidden declarations or hollow definitions were found. Verdict: pass.
3. Checked the affine-chart statement against its Lean type and node, and searched the
   library/DAG for duplicate declarations. It is a strictly smaller single-chart reduction,
   with the required source, proof plan, and node. Verdict: pass.
4. The local proof uses the affine-chart result, finite-subcover construction, and explicit
   pullback transport; no shorter available library route was found. The removed direct
   colimit import is now used by the affine-chart module, so no additional pruning applies.
   Verdict: pass.
5. Verified that both nodes' Lean records, proof dependencies, proof origins, and the unit
   route agree with the delivered code; the unit's realized route is not bypassed. Verdict:
   pass.

Changed only the report by adding this second-reading record; no Lean code or DAG content was
altered during the second reading.
