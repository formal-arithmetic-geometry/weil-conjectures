## What changed

The item keeps its public imports, definitions and theorem signature unchanged.
Its proof now uses open full faithfulness and ordinary support, rather than
normalizing an explicit ordinary base-change map against the derived square.
Private helpers establish the ordinary open unit, its derived unit, and the
derived open counit on pullbacks of extensions. The last step expands the actual
inverse transpose as extension of an isomorphism followed by that counit.

Proof imports added: ProEtaleOpenSlicePresentation,
SubterminalModuleLocalCalculus (including its proved private unit lemma), and the
new IntegralRingedOpenPullSupport. The new module states only ordinary support
preservation for arbitrary ring sheaves. The item node follows the implemented
full-faithfulness, localization and inverse-transpose argument. Both modules
passed the final remote compilation without warnings, with development profiling
removed. The compile service enforces its 60-second limit on Lean itself; its
displayed elapsed totals also include setup.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralRingedOpenMate_isIso`
(node `lem-sf-integral-ringed-open-base-change`). There are no sorries in the item.

Added one hole in
`AlgebraicGeometry.Scheme.proEtaleRingPullback_openSupport`
(node `lem-sf-ringed-pullback-ordinary-open-support`). This is a decomposition:
1 original hole closed, 1 ordinary support hole added, net 0 holes closed. The
remaining statement has no derived categories, no completed coefficients, no
specified exchange transformation and no module-pullback compositor. The
combining proof supplies the ordinary and derived unit arguments, the degreewise
counit argument and its exact localization, and invertibility of the actual mate.

## No longer needed

No original imports, modules or nodes are withdrawn. The original three declared
dependencies remain needed. No modules are pruned.

The proof does not need a separate normalization theorem comparing an ordinary
base-change transformation with ringedSquare: after full faithfulness and support,
any invertible square comparison gives an invertible inverse transpose. No new
normalization or complex-exchange lemma was introduced.

## Where the brief, the DAG or earlier work was wrong

No existing statement was changed or marked disputed. The plan can be shortened
by using essential-image membership instead of constructing a specified ordinary
exchange and its inverse on generators.

The existing finite-coefficient open exchange cannot be specialized to arbitrary
completed ring sheaves. The ringSheaf_baseChange_mates theorem additionally
requires quasi-compactness and quasi-separated ambient schemes and a
quasi-compact open; none may be added here. The arbitrary-ring
proEtaleOpenRestrictionCounit theorem does apply to a chosen fibre product with
canonical inverse-image coefficient rings. The new support node records how to
transport its right-adjoint comparison through the three coefficient
isomorphisms and the cartesian-square isomorphism, then take left adjoints. That
ordinary transport remains to be formalized.

Edge cases checked mathematically: identity and empty opens, zero coefficient
rings, independently twisted coefficient isomorphisms, and arbitrary unbounded
complexes. No argument uses geometric-point conservativity or quasi-compactness.
The blueprint searches found finite/constant and constructible open-base-change
statements, rather than this arbitrary-ring ordinary support statement.

## New nodes

`lem-sf-ringed-pullback-ordinary-open-support`, in
`Sheaf.SixFunctors.IntegralRingedOpenPullSupport`, isolates preservation of the
ordinary open essential image. Its proof plan follows ringed localization
(Stacks 04J0), the arbitrary-ring open-slice presentation and the existing open
restriction/direct-image comparison; uniqueness of left adjoints gives the
required witness. Actual LeanSearch, LeanFinder, Loogle and Mathlib grep results
are recorded. No change record is needed: no existing public interface changed.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
