## What changed

Replaced the remaining proof of
`WeilConjectures.sfOrientationIntegralLineMaps_existsUnique` without changing its statement.
The proof constructs the normalized first-line map and uses the existing signed-power
comparison, proves the scalar/root formula by two-step induction, and proves uniqueness
under the module adjunction using local root-generator extensionality.

Added `Sheaf.Paper.FirstRootLinePullback` and `Sheaf.Paper.PositiveRootGeneratorExt`.
The latter also contains the proved private cover helper with its auxiliary universe
fixed explicitly, and `sfIntegralPositiveRootLineMaps_exists`, the complete
existence-and-normalization part of the original argument. That proof is separated
to meet the per-file time limit; it adds no hole. Its narrow cover signature avoids
carrying unrelated derived clauses into the power proof, and keeps the first-line module's transport instances
private from the main module.
The first-line proof uses the specified coefficient projections and root projections,
normalized integral tensor transport, and invertibility of the underlying module-unit
comparison. No primitive root, arbitrary line identification, or new coefficient system
is chosen. Edge cases checked: exponent zero is the scalar unit, exponent one
is the normalized first line, and all universal-property arguments apply to the
empty scheme. The generator-extensionality statement needs no invertibility
hypothesis because it concerns only the constructed scalar extension and tensors. Existing
shifted-complex, tensor-unit and pull-unit proofs are retained.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.sfOrientationIntegralLineMaps_existsUnique`
(node `def-sf-orientation-integral-line-comparisons`).

Proved the supporting theorem `WeilConjectures.sfFirstRootLinePullback_exists`
(node `lem-sf-first-root-line-pullback`) from existing declarations. This builds
the normalized additive comparison, lifts its adjunct to a module map, and
reflects invertibility through the forgetful functor.

Added one smaller hole: `WeilConjectures.sfPositiveRootGenerator_hom_ext`
(node `lem-sf-positive-root-generator-ext`). This is only extensionality of maps out
of the constructed unshifted positive powers: it has no scheme base-change map,
no construction of a comparison, and no isomorphism assertion. The original theorem
is reduced to it by the actual construction, induction, and adjunction argument.
This is a decomposition, with one hole closed and one added; the item module has
zero remaining holes. The supporting first-line proof uses the project's existing
named proof dependencies, as permitted by stage 3. The final server batch compiled
all three modules successfully (exit code zero).

## No longer needed

No existing import, module or node is withdrawn. All previous dependencies remain
needed by the retained complex-product, good-complex and completion-unit proofs.
The scheme-isomorphism-only
`FrobeniusCoefficientTwists.existsUnique_positiveLineMaps` is not used to prove
the arbitrary-map comparison, since its extra scheme-isomorphism hypothesis does
not hold here. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing DAG described the completed tensor and pull-unit proofs, but explicitly
left the arbitrary-map line theorem open. The new initial proof steps record its
first-line construction, power extension, generator calculation, and uniqueness.
The existing Frobenius positive-line theorem has an `IsIso g` assumption, so it
cannot directly close this hole. The more general signed-power construction in
`CartesianCoefficientTwists` supplies the needed power recursion once the first
line has been constructed.

The rework table lists an old quarantine for this module. The current item source
is present, was copied intact, and its Lean attachment and prior dependencies are
preserved. No archive or parent is withdrawn.

A read-only dependency traversal found no cycle through the item node or either
new node. It did encounter unrelated existing cycles in the shared DAG, for example
`lem-pc-ring-hom-extension-differential` →
`lem-pc-ring-hom-extension-differential-adjacent` →
`lem-pc-ring-hom-extension-differential`. Those records are outside this delivery.

## New nodes

`lem-sf-first-root-line-pullback` records the scalar/root-normalized ordinary
module pullback of the first integral line. Its proof linearizes the normalized
additive tensor transport and cancels the invertible forgotten module unit.

`lem-sf-positive-root-generator-ext` records the local pure-root uniqueness step
used under the module adjunction. Its docstring and node give the scalar-extension
and tensor-sheafification proof, including exponent zero and the empty scheme.

Blueprint searches for `root line` and `tensor generators` found no matching
statement (the latter only found the unrelated frame-class definition). The
ancestor check gives `sk-def-sf-orientation`; both new nodes keep that ancestor.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
