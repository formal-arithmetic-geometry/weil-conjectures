## What changed

Replaced the entire proof hole of
`AlgebraicGeometry.Etale.vectorIntegration_presentationIso` by a complete Lean reduction
from an affine-coordinate trace lemma. The original theorem signature and its two public
imports are unchanged. All five new imports are private proof imports.

The proof constructs a simultaneous frame cover of the two bundles, restricts their
module frames to the intersections, and uses the universal property of the two pullbacks
to construct an actual automorphism of the affine coordinate tower on each intersection.
The automorphism is not assumed linear. The code proves the coefficient-pasting equation,
the compact-support exchange-pasting equation including its identity comparison, and the
identification of the original chart coefficient with the generic Cartesian coefficient.
The existing Cartesian-prefix action theorem then identifies the remaining local factor
with the action of this affine automorphism.

The defining normalizations of the two integrations give the local counits. After the
affine-coordinate lemma removes that action, the code cancels the constant-object
comparison and descends the resulting equality. This descent is proved explicitly:
fullness of the degree-zero embedding produces sheaf maps, its restriction correspondence
identifies their local images, and joint faithfulness of the surjective frame cover
identifies the global maps. It does not assume faithfulness of restriction for arbitrary
derived objects.

Added `Sheaf.Paper.AffineSpaceIsoTraceInvariance` with one named obligation concerning only
an automorphism of a single affine coordinate tower. It has no bundle modules, arbitrary
bundle presentations, frame covers, or sheaf-gluing conclusion. This is the affine trace
part of the original node's first proof step, while all bundle geometry and descent are
implemented in the item. No existing dependency or source-library module was changed.
Updated the item's proof plan and dependencies and added the new lemma's node.

Validation: the final item compiled on the project server in 20.3 seconds, without
warnings or profiling options. The new affine module compiled separately in 6.8 seconds.
The coefficient transport is calculated as an equality of isomorphisms: converting
that calculation to a component-level transported equality caused excessive kernel
normalization, whereas the delivered isomorphism-level proof is fast.

## Proved and sorry left

Original holes: 1. Closed the whole original proof hole of
`AlgebraicGeometry.Etale.vectorIntegration_presentationIso`
(node `lem-pur-vector-integration-presentation-iso`). There is no `sorry` in that module,
including in any of its private helpers or the restricted-frame construction.

Added holes: 1, exactly the entire theorem proof of
`AlgebraicGeometry.Etale.affineSpaceIsoTraceInvariance`
(node `lem-pur-affine-space-iso-trace-invariance`). Its module has no other declarations
or holes. Its docstring and node explain the normalized rational-point degree argument
and geometric-stalk detection, including rank zero, empty bases and the zero ring.

This delivery is a decomposition, with one upper hole closed and one strictly smaller
affine-coordinate hole added; it claims no net reduction in the number of holes. The
composition from the smaller assertion to the original statement is actual checked Lean,
not application of the same theorem under another name or a repackaged hypothesis.

## No longer needed

No original import was removed and no entire existing module is claimed pruned. The
item's global descent no longer directly invokes geometric-stalk conservativity or the
unbounded compact-support comparison package: it uses the surjective frame cover and the
existing exchange-pasting API. Accordingly
`lemma-weil-pbc-geometric-stalk-conservative` and
`lem-amb-unbounded-compact-support-comparisons` are not direct proof dependencies of the
item's new route. Their mathematics is still needed below the new affine-coordinate
lemma or the exchange API, so they are not claimed globally unnecessary. Degree-zero
full faithfulness remains used, both directly and through `EtaleDegreeZeroHom`.

The implemented frame comparison uses the already available
`vectorIntegrationCartesianPrefix_action`, whose signature permits arbitrary
endomorphisms even though its docstring calls the action linear. No new chart-prefix,
base-change, frame-comparison or sheaf-descent hole is introduced.

## Where the brief, the DAG or earlier work was wrong

The listed affine top-trace theorem gives a trace isomorphism and compatibility with
changes of base, and linear trace invariance gives its compatibility with invertible
matrices. Neither signature supplies invariance under an arbitrary nonlinear affine-space
automorphism. The assigned theorem really allows such an automorphism. No linearity or
zero-preservation assumption was added and no conclusion was weakened.

The existing Cartesian-prefix theorem is more general than its linear wording: its
parameter is an arbitrary map together with a Cartesian square over the identity, rather
than a matrix. This permits reusing it for the nonlinear coordinate change produced by
pullback uniqueness. The genuine remaining trace-normalization question is isolated in
the single affine-coordinate lemma, instead of assuming that the linear theorem covers it.

The unit `sk-prop-an` route is preserved, and no smooth-purity or exceptional-inverse-image
compatibility theorem is used to prove a compatibility on which it could depend. The new
statement's edge cases were checked in the mathematical argument: for d=0 the projection
and the automorphism over it are identities; for empty S or A=0 the relevant maps are
unique. The frame-cover proof needs no nonempty-cover hypothesis.

## New nodes

`lem-pur-affine-space-iso-trace-invariance` is attached to
`AlgebraicGeometry.Etale.affineSpaceIsoTraceInvariance` in
`lean/Sheaf/Paper/AffineSpaceIsoTraceInvariance.lean`. It is the normalized trace assertion
for one coordinate affine space, extracted from the original node's fibre-degree step.
Its proof plan records the rational-point normalization, degree-one pullback under an
isomorphism, and degree-zero geometric-stalk detection. Three Mathlib search methods and
the project search found no existing declaration with this nonlinear generality. The
parent now implements the separate work needed to pass from this special affine model
to two arbitrary bundle presentations.

No change record is needed: all existing public signatures, public imports, definitions,
instances and attributes remain unchanged; elaboration attributes are local to the item.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AffineSpaceIsoTraceInvariance": "b5bf25b5c7da620ca11e6b53dbd8bd9610749210", "Sheaf.Paper.VectorIntegrationPresentationIso": "30a6fee9817d1fcd23bea10bd966fbb708201e15"}, "results": {"Sheaf.Paper.VectorIntegrationCartesianTrace": {"hash": "6d9af034860673ac663b2b3db4dcfcf09fdfc934", "status": "OK"}}, "seconds": 37, "time": "2026-10-28T06:53:47+0800", "transitive": 0, "version": 1}
```

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
