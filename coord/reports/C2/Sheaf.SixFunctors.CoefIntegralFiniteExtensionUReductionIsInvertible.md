## What changed

Added the proof-only module
`Sheaf.SixFunctors.CoefIntegralFiniteExtensionFiniteUIsInvertible` with the
strictly simpler finite-level theorem `finiteU_isIso`.  The item now imports
that theorem and proves `comparison_reduction_isIso_u` by rewriting with
`u_reduction`, installing the isomorphism instances for the quotient,
reduction, scalar extension, and finite counit maps, and cancelling the target
reduction isomorphism with `IsIso.of_isIso_comp_right`.

## Proved and sorry left

Closed the item hole `WeilConjectures.IntegralFiniteExtension.comparison_reduction_isIso_u`.
The new helper theorem remains one named split-off `sorry`:
`WeilConjectures.IntegralFiniteExtension.finiteU_isIso`, in node
`lem-sf-integral-finite-extension-finite-u-is-invertible`.
No definition contains a `sorry`; the delivery has one remaining theorem hole,
which is the finite-free counit calculation itself.

## No longer needed

The item proof directly uses only `def-sf-integral-finite-extension-core` and
the new finite-level helper.  It does not directly import or use the planned
nodes `lem-coef-finite-free-extension`, `lem-coef-finite-dualizing`,
`lem-coef-normalized-dvr-effectivity`, or
`lem-sf-integral-finite-dualizing-coherence`; those remain dependencies of the
new helper's proof plan where the finite-free calculation belongs.
No existing module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof step bundled the finite-free counit calculation with the
cancellation argument and supplied no Lean declaration for the former.  The
finite-level assertion `IsIso (finiteU ...)` is a strictly simpler intermediate
statement, so it is split into its own node.  The parent reduction proof is
complete from that declaration and the defining equation `u_reduction`.

## New nodes

- `lem-sf-integral-finite-extension-finite-u-is-invertible`: the finite-free
  quotient-level counit comparison `finiteU` is an isomorphism.  Its Lean
  declaration is `WeilConjectures.IntegralFiniteExtension.finiteU_isIso` in
  `Sheaf.SixFunctors.CoefIntegralFiniteExtensionFiniteUIsInvertible`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionFiniteUIsInvertible": "4f1d6241e13b0c4977d43d4186dc8e625be4e513", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReductionIsInvertible": "cfb452e2295d186a8381d3f195fb669318a0be9b"}, "results": {}, "time": "2026-10-28T09:59:39+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
