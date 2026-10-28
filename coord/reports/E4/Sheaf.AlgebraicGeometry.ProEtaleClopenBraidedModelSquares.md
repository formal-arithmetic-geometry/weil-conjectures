## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_model_squares`
with its entire signature unchanged. The tensor square uses the existing private
`inverse_tensor_square_aux`, the native `isIso_mu` and `tensorIso_hom` API, and hcδ.
Naturality of the factors comparison along the native total-tensor identity aligns its
displayed component. Only hP and hiP are needed for cancellation; all given hypotheses stay.

The unit square is completely proved in the new module
`Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedUnitSquare`, as
`AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_unit_square`.
Its signature omits the total tensor comparison b and all tensor or K-flat hypotheses.
It uses the existing native unit-isomorphism API, monoidality of factors, hcη,
functoriality, associativity, and isomorphism extensionality. The existing proved private
`inverse_unit_square_aux` moves to this unit module and handles the supplied two-factor
cochain unit generically, reducing concrete type-checking work. The tensor helper stays
in the item.
The item privately imports the unit theorem and combines it with its tensor calculation.

Updated the item's proof record and added a node for the proved unit theorem. No other
existing module, definition, signature, public import, or node is changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_model_squares`
(node `lem-pur-clopen-braided-model-squares`). Also completely proved
`AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_unit_square`
(node `lem-pur-clopen-braided-unit-square`). There are zero remaining holes in either
module, zero holes added, and zero split-off unproved statements. Both private categorical
cancellation helpers and the private projection lemma for `unitComparison` have complete
proofs. The new unit node carries no further work.

Final clean server compile: unit module 45.3 s, assigned module 47.1 s, no warnings.
A temporary importing module inspected both public theorems with `#print axioms`: each
depends only on `propext`, `Classical.choice`, and `Quot.sound`. That temporary module was
removed before delivery; neither proof depends on `sorryAx`.

## No longer needed

Removed the private imports
`Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedLocalization` and
`WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex`: the native API is already
publicly imported by the normalization interface, and the cochain and derived braided
structures are supplied as arguments. Removed the disable directive for
`Functor.mapCochainComplexMonoidal`, whose declaration was supplied only by the latter
private import. No public import is removed.

The existence results `lem-pur-clopen-braided-cochain-normalization` and
`lem-pur-clopen-braided-localization` are not used by this cancellation proof: c and d
are supplied structures. The construction of those structures remains needed by the parent
normalization theorem, so no existing module or node is withdrawn or claimed globally
unnecessary.
`lem-sf-ringed-derived-native-tensor` remains needed, directly for the tensor computation
and through the new proved unit theorem. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Corrected the assigned file's two docstring
blueprint tags from its parent node to `lem-pur-clopen-braided-model-squares`. The current server queue lists a one-hole proof
item, with no rework row or build-error record. The cancellation argument applies to
zero coefficient rings, empty schemes and unbounded complexes without extra assumptions.

Profiling the complete proof located the cost in kernel checking of comparisons between
native monoidal structures, especially the unit isomorphisms. Tried explicit tensor/unit
API equations, definition-only reduction, caching monoidal structures locally, an abstract
iso-valued unit cancellation helper, and using native lax structures directly. The complete
single-file versions still exceeded 60 seconds. The tensor and unit proofs individually
compiled within 60 seconds. The final two modules therefore separate these logically
independent equations, with all proofs complete and all shared definitions unchanged.
No profiling options remain in the delivery.

The latest blueprint puts the purity-conventions unit under `sec-six-functors-basics`;
its statement and route stay unchanged. The new unit theorem uses the same generic native
unit comparison tool already used by the assigned node.

## New nodes

`lem-pur-clopen-braided-unit-square`, at
`dag/nodes/sec-smooth-purity/lem-pur-clopen-braided-unit-square.json`, records the fully proved
canonical unit equation. This is just the unit clause of the assigned argument; it has no
bifunctor comparison or model-normalization conclusion. Its source is the original node's
unit cancellation step, Stacks Tags 06YU and 0FPT. It is needed by the item and introduces
no sorry. No change record is needed: only the assigned module, a new proved module and
their own nodes are delivered.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelSquares": "70aa719ed44b707c88729bd2d97ab0c0a48aa48e", "Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedUnitSquare": "8f5ef1d81136b775bf0639fc4cdf3b7537bb2c15"}, "own_failed": ["Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedUnitSquare", "Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelSquares"], "results": {}, "time": "2026-10-28T10:09:17+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
