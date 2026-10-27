## What changed

Proved `WeilConjectures.LocalFrobeniusLarge.weilIterate_add` from the
three-pullback naturality/reassociation equation
`WeilConjectures.LocalFrobeniusLarge.composition_map_assoc`, in the new module
`Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence`.

The actual Lean argument proves the scheme-power addition identity, unfolds the
successor Weil iterate, distributes functor maps over composition, applies the
three-pullback equation, postcomposes it, and transports the induction hypothesis
along the scheme-power equality. Private helpers prove the required heterogeneous
postcomposition and dependent-function transport. The theorem's signature,
definitions, original docstring, public import and unit route are unchanged.
Only the new coherence module is added as a private proof import.
The two-module server compile accepted both files; its sole formatting warning
was repaired before submission to the delivery checks.

Updated the item's DAG proof to match this induction. The missing common-stage
compositor equation is a new sourced node, rather than an assumption about the
Weil iterates. Its statement concerns three arbitrary scheme endomorphisms and
one arbitrary common-stage arrow, contains no Weil complex or iterate, and is
exactly the first step of the original plan. Its docstring explains integral
coherence, rational pure tensors, and common-stage representative descent.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.LocalFrobeniusLarge.weilIterate_add`
(node `lem-zl-large-weil-iterate-addition`): the item now has zero direct holes.

Added one hole in
`WeilConjectures.LocalFrobeniusLarge.composition_map_assoc`
(node `lem-zl-large-composition-map-assoc`), whose whole proof is `:= by sorry`.

This is a decomposition: one original hole closed, one strictly separate
compositor-coherence obligation added, net hole reduction zero. The iteration
induction and its equality transports are complete Lean proofs; no definition
contains a hole. No claim is made that the resulting theorem is independent of
`sorryAx` before the new obligation and existing imported obligations are proved.

## No longer needed

None. No imports or modules are removed. The original integral-composition,
common-stage operations, coefficient-category and local-Frobenius prerequisites
remain needed by the new coherence step. The parent's direct proof dependencies
now name that step and the local-Frobenius definitions; this is factoring the
same route, not pruning those prerequisites from the closure.

## Where the brief, the DAG or earlier work was wrong

The original plan's first step requires an actual common-stage coherence
calculation. `integralPullbackComposition` exposes integral naturality and
associativity, but `LocalFrobeniusLarge.composition` is defined componentwise,
not as a natural isomorphism equipped with those laws. The definitions of
`commonStageDerivedPullback` prescribe maps on arbitrary representatives, so
one cannot apply integral associativity directly to a common-stage Weil arrow.
The new obligation isolates precisely this missing passage, including arbitrary
rational arrows; it assumes no invariant integral lattice.

Searches covered the existing dependency declarations, Mathlib, both library
roots, and the private naturality proof in `SemilinearFieldOperationLifts`.
The latter uses `pullbackTensorCommonComposition`, a differently specified
compositor; importing that private proof cannot prove an equation about the
present compositor. LeanFinder returned generic pseudofunctor/descent laws;
LeanSearch returned generic derived-natural-transformation equations. Neither
identifies the prescribed components. The Loogle query `Functor.map_comp`
reported an unknown unqualified identifier, so no absence conclusion is drawn
from it. All three successful search kinds are recorded on the new node.

Edge cases: the induction base `b = 0` is the actual successor recursion;
`a = 0` needs no pullback unit. The coherence statement allows zero objects,
zero arrows, identity scheme maps and arbitrary rational arrows. With `t = 0`
both composites vanish by functoriality and zero composition; with identity
arrows it reduces to compositor associativity. Source associativity is retained
as HEq, so no extra chosen comparison or equality of endpoints is assumed.

## New nodes

`lem-zl-large-composition-map-assoc`, realized by
`Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence` and
`WeilConjectures.LocalFrobeniusLarge.composition_map_assoc`, records the
three-pullback reassociation/naturality step. Sources read: Stacks 099N,
parts (2),(5), and 0D6D's K-flat proof; the existing integral composition and
rational/common-stage operation signatures and definitions. Its proof in words
explains the localization and representative calculation that remains to be
formalized. The parent retains the original blueprint and unit route. No change
record is needed: no existing public signature, definition, attribute or public
import is changed.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
