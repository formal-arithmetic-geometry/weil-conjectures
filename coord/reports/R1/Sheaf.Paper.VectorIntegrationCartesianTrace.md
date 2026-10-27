## What changed

Replaced the hole in `WeilConjectures.PurityFiniteSetting.vectorIntegration_cartesianTrace`
by a calculation from canonical tensor-pullback base change and fixed-base presentation
isomorphism invariance. The comparison isomorphism is constructed by `IsPullback.isoIsPullback`;
its projection equations, actual compact-support exchange pasting, pullback associativity,
exchange naturality and constant-to-unit compatibility are proved or applied explicitly.
The existing statement and public import remain verbatim. All added imports in the item are private.

Added `Sheaf.Paper.VectorIntegrationPresentationIso`, containing only the smaller fixed-base
isomorphism-invariance theorem. Updated the item's proof steps and dependencies and added the
new theorem's DAG node. No other existing Lean module or node is changed.

Also added the fully proved `Sheaf.AlgebraicGeometry.OrdinaryFiniteSingleUnitPullback`
with `AlgebraicGeometry.Etale.ordinaryFiniteSingleUnitPullback_hom`. This factors the
constant-to-unit comparison out of the item: after local irreducibility and a generic
exchange calculation improved elaboration, kernel checking of this independent step
still consumed about 20 seconds of a 59-second compile. Its extraction adds no hole.

Validation: single-file compilation succeeded without warnings for the item (43.1 s),
the proved unit comparison (28.3 s), and the fixed-base lemma (7.8 s). All are below
the 60-second limit. The original theorem signature and public import are byte-identical;
the new Lean signatures match their node records, and all Lean lines fit 100 characters.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.vectorIntegration_cartesianTrace`
(node `lem-pur-vector-integration-cartesian-trace`). Its proof contains no `sorry`.
The private coefficient-pasting, exchange-pasting, composition-transport and generic
trace-pasting helpers are complete proofs. The separate public theorem
`AlgebraicGeometry.Etale.ordinaryFiniteSingleUnitPullback_hom`
(node `lem-pur-ordinary-finite-single-unit-pullback`) is also proved with no `sorry`.

Added one hole, the whole proof of
`AlgebraicGeometry.Etale.vectorIntegration_presentationIso`
(node `lem-pur-vector-integration-presentation-iso`). This is a decomposition: one upper
hole closed and one strictly smaller hole added in this packet; no net proof is claimed.
The new obligation concerns two bundle presentations over the SAME base and an isomorphism
of their total spaces. It has no morphism between different bases and no Tate base-change
transport between bases. The parent separately proves how to combine this fixed-base
geometric invariance with the already proved canonical base-change theorem.

## No longer needed

No original imports were removed and no whole module is claimed pruned.
The two constant-unit proof imports are used by the new proved comparison module.
They are no longer imported directly by the item. The original
`VectorPurityBaseChange` public import is preserved. The parent no longer directly requires
`lem-amb-affine-space-top-trace`, `lem-pur-degree-zero-derived-map-gluing`,
`lemma-weil-pbc-geometric-stalk-conservative`, `lem-asd-etale-finite-twist-pullback`, or
`lem-amb-unbounded-compact-support-comparisons` as separate proof steps: its complete
calculation uses canonical base change, fixed-base invariance, exchange pasting and the
native constant-unit comparison. Their underlying mathematics remains required in the
canonical theorem or the new fixed-base node; none is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The declared canonical base-change theorem applies only to the symmetric-algebra map
of the tensor-pulled-back module. An arbitrary Cartesian presentation need not be linear
or preserve zero. Thus invertible-matrix trace invariance alone does not justify replacing
its top map by an arbitrary presentation isomorphism. The original plan correctly calls
for degree invariance on geometric fibres, but this fixed-base assertion is not present
in the signatures of its listed dependencies. It is isolated in the new theorem, rather
than assuming that the canonical theorem already covers arbitrary presentations.

The unit sk-prop-an route and every target statement are preserved. The new statement was
checked at d=0, on the empty base, and with the zero coefficient ring: the degree-one and
identity comparisons give the asserted equations. No exceptional-inverse-image theorem
or smooth-purity compatibility is used, so there is no circular route through the parent.

## New nodes

`lem-pur-vector-integration-presentation-iso` attaches the single new theorem in
`lean/Sheaf/Paper/VectorIntegrationPresentationIso.lean`. It isolates proof step 2 of the
original node: invariance of the actual integration under an arbitrary total-space
isomorphism over a fixed base. Its docstring and node give the geometric-fibre degree
argument and descent. Searches of Mathlib, the whole blueprint and project declarations
found no existing theorem with this generality; translations and linear actions are
special cases, and the existing normalized Cartesian trace theorem depends on this item.
No existing interface is changed, so there is no change record or forced adaptation.

`lem-pur-ordinary-finite-single-unit-pullback` attaches the fully proved native
constant-to-unit equation in
`lean/Sheaf/AlgebraicGeometry/OrdinaryFiniteSingleUnitPullback.lean`. This is the
constantUnit_pullback equation transported by constantUnit_hom at the two ends.
Those already proved nodes from the projective-line unit are used only as coherence
tools, preserving the smooth-purity unit route. It adds no mathematical assumption
and no hole; the separate file keeps kernel conversion work below the per-file limit.
Its Mathlib searches found no equation in these project-specific definitions.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.OrdinaryFiniteSingleUnitPullback": "9727a76084dd8a917fc42f9bd075912d885c5e95", "Sheaf.Paper.VectorIntegrationCartesianTrace": "6d9af034860673ac663b2b3db4dcfcf09fdfc934", "Sheaf.Paper.VectorIntegrationPresentationIso": "f7825d8fa1073eed7d976dbf16d989030f069ab9"}, "results": {"Sheaf.Paper.NormalizedVectorPurityBaseChangeComponent": {"hash": "76246c1aa0e61bbce223a671dfb2826b0a1e4b7e", "status": "OK"}}, "seconds": 90, "time": "2026-10-28T04:31:17+0800", "transitive": 0, "version": 1}
```

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
