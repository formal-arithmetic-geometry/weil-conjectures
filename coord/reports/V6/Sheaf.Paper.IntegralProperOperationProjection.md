## What changed

Replaced the hole in `integralProperOperationProjection_isIso` by an explicit categorical
transport argument. Private helpers prove invertibility of mates under fully faithful
restriction, identify the completed and ordinary derived direct images, and obtain the
ordinary proper counit projection from the identity-open compactification. The ordinary
projection is proved invertible by the existing finite-reduction theorem and conservativity.
Only proof imports are added to the existing module; its public import and theorem signature
are preserved. Validation uses single-file Lean compilation and the delivery tool's
compilation and preflight checks.

Added `Sheaf.Paper.IntegralOrdinaryTensorPullbackNormalization`, which isolates the remaining
left-operation tensor/pullback normalization square. The componentwise currying helper
`ordinaryCurriedTensorPullback` is constructed and proved directly, with no hole. This assertion contains no direct
image, projection morphism, counit or projection-invertibility conclusion. Its docstring
records the representative-level argument, including the strict Roos shifted coordinate.

## Proved and sorry left

Closed the original hole in `WeilConjectures.integralProperOperationProjection_isIso`
(node `lem-sf-integral-proper-operation-projection-isomorphism`). The item has zero holes.

Added one hole: `WeilConjectures.integralOrdinaryTensorPullbackNormalization`
(node `lem-sf-integral-ordinary-tensor-pullback-normalization`). This is a decomposition:
one hole closed, one strictly simpler hole added, net zero holes closed. All categorical
transport, identity-open specialization and invertibility arguments are proved in Lean.
No other holes are added or changed.

## No longer needed

No existing public import is removed, and no module is withdrawn or globally pruned.
The separate completion-unit cancellation is unnecessary: finite reductions prove
invertibility of the ordinary projection directly. The proof still imports the pro-etale
projection module for its constructible-domain lemmas. The original constructible tensor
completion and ordinary/completed pullback dependencies remain needed through the new
left-operation normalization node. No unit statement or realized proof step is removed.

## Where the brief, the DAG or earlier work was wrong

The stated normalization step did not have a declaration for its actual tensor/pullback
compatibility square. Separate invertibility of tensor completion and ordinary pullback
does not supply that square. The new node states precisely this remaining left-operation
step, without restating the proper projection obligation under a new name.

The public integral projection-formula component asks for auxiliary Tor and origin data,
while its existing finite-reduction proof works for the present constructible inputs
without these arguments. The proof uses that finite-reduction theorem directly. No
separatedness of the structure schemes or additional Tor hypothesis is introduced.

## New nodes

`lem-sf-integral-ordinary-tensor-pullback-normalization`, in
`dag/nodes/sec-six-functors/`, records the natural tensor and pullback comparisons on
constructible inclusions and their compatibility with the prescribed canonical maps.
It is a left-operation coherence step from the integral reconstruction of the source,
and is strictly simpler than proving a proper right-adjoint projection invertible.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
