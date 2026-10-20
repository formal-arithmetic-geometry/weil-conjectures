## What changed

The assigned module keeps all fourteen existing public signatures and public imports.
Its three holes are closed. The geometric adjunction descends finite-stage units and
counits; its triangles are checked at finite-stage inclusions. Private mate lemmas prove
right-family coherence and transformation compatibilities from the counit mate equation.
The representative formulas identify the descended left functor with actual pullback.

`SfIntegralPullbackLinearAdjunction` now completely proves the integral adjunction using
the actual whole-system adjunction. An explicit fully faithful reduction helper uses
invertibility of the reconstruction unit on complete constructible objects. The actual
normalized pullback counit supplies the comparison for `Adjunction.restrictFullyFaithful`.
The right functor is the existing `directImageFunctor`, with its existing coefficient
linearity. This closes one of the two lower holes inherited from the interrupted attempt.

`SfRationalDirectImageAdjunction` proves raw Hom localization of that integral
coefficient-linear adjunction. Its unit and counit are tensored with one. Tensor induction
proves naturality and both triangles; the pure-tensor characterization identifies the
left functor. The integral adjunction concerns arbitrary finite-type maps, including
nonseparated maps.

The separate coefficient-change source result remains in
`SfRationalDirectImageCoefficientCompatibility`. It uniquely specifies the coherent left
stage family by its literal functors and every comparison component. For each already
specified pointwise adjunction it asserts invertibility of the literal right mate.
It asserts no adjoint existence. Thus it selects no arbitrary family data from mere
existence. The consumer constructs pointwise adjoints and proves the mate counit equation.

Two proved identity-comparison modules establish scalar-compatible rational identity
pullback and its descent. These identify the actual Frobenius pullback as an equivalence.
The Weil adjunction uses `IsoAlgebra.mate`; its forgetful comparison is `rightAdjointUniq`,
and the prescribed counit equation proves uniqueness.

The two existing adjunction definition proofs use `delta` instead of `unfold`, retaining
`Adjunction.ofIsLeftAdjoint` with its explicit proof. The compact-support module held by
K9 has exactly one ordinary import removed to break a cycle and permit the system route.
No signature, public import or declaration body of that module changes. The packet has
seven Lean modules: six modules for the assigned proof and its lower results, plus this
import-only adaptation. Five of the six proof modules have zero holes.

## Proved and sorry left

Original assigned holes: three. Assigned holes remaining: zero.

* `WeilConjectures.sfModelPull_isLeftAdjoint`: complete finite-stage construction,
  raw rationalization, mate coherence, descent, triangles and representative identification,
  using the one separate coefficient-change result below.
* `WeilConjectures.sfModelWeilPull_isLeftAdjoint`: complete Frobenius-equivalence and
  Weil-adjunction proof from the geometric adjunction.
* `WeilConjectures.sfModelWeilDerivedPush_forget`: complete counit-normalized unique
  forgetful-comparison proof.

The new declarations `WeilConjectures.sfIntegralPullbackLinearAdjunction`,
`WeilConjectures.sfRationalDirectImageAdjunctions`,
`WeilConjectures.coherentRationalPullbackIdentity`, and
`WeilConjectures.commonStageDerivedPullback_identity` are proved. All private helpers
are proved. In particular the integral adjunction no longer contributes a new hole.

One lower hole is added:
`WeilConjectures.sfRationalDirectImageCoefficientCompatibility`, node
`lem-sf-rational-direct-image-coefficient-compatibility`. It is the source's normalized
coefficient-tower and finite-free geometric scalar-mate result. Taking a mate alone does
not prove invertibility. The system interface defines `systemDirectScalar` but does not
assert its invertibility. Existing operation-exchange results with that assertion impose
separatedness, absent here. The retained lemma has its own source, full proof in words and
DAG node. Its functor and comparison data are uniquely fixed, including identity or repeated
coefficient fields. The statement covers zero objects, empty schemes and nonseparated maps.

The adapted compact-support module's two original theorem holes are unchanged; this
packet adds none there. Thus three assigned upper holes are closed and one strictly lower
source result is split off, for net two holes closed. This includes decomposition and is
not claimed as three unconditional proofs from a hole-free library.

## No longer needed

The old arbitrary-field/Verdier route is unused:
`arbitraryFieldPullback_isLeftAdjoint`, `Sheaf.SixFunctors.ArbitraryFieldVerdier`,
`Sheaf.Paper.AdicClosedConstructible`, `Sheaf.Paper.AdicExceptionalProjection`, and
`Sheaf.Paper.FiniteResidueDualizing`. Its provisional relocation, imports, node edits and
change record are absent. No global pruning credit is claimed for that discarded attempt.

Ordinary imports removed from the assigned module:
`CompletedCoefficientPushforwardComparison`, `SfIntegralDirectImageConstructible`,
`SfIntegralConstructible`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`,
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, and
`PbcDescentFunctors`. Some remain lower dependencies. Direct `StageSystem.Morphism`
descent replaces the generic PBC descent application. All original public imports stay.
The finite-adjunction statements need `WeilIndSheafCategory`, not
`SfCommonStageWeilCohomology`. The provisional `Adjunction.FullyFaithful` proof import
is removed. Rationalization directly imports `TensorProduct.Map`.

The proved integral lemma uses `SystemOperationExchangeRealization`. It no longer needs
the provisional direct route through `CompletedPullbackAdjunction`,
`CompletedCoefficientPushforwardComparison` or `PbcScalarExtension`; the system realization
already supplies the normalized concrete adjunction. These source dependencies remain
where the system theory needs them. The fully proved provisional
`SfCompletedDirectImageConstructible` module and node are scratchpad only.

The single ordinary `SfCommonStageDirectImage` import is removed from
`SfIntegralCompactSupportConstructible`; its public imports and all declarations stay.
No landed module is withdrawn. No unit statement or required unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The interrupted packet treated the system interface as unusable because its compact-support
closure formed an import cycle. The cycle is caused by one unused ordinary proof import.
The launcher's explicit import-removal exception permits this minimal adaptation, checked
by the independent reader. Removing that edge makes the existing system adjunction
available and closes the integral hole instead of retaining a second decomposition.

A scheme automorphism does not itself register an equivalence for the selected
common-stage pullback; the identity-comparison nodes prove the required fact.

The previous dry run passed preflight at `c7249ef0f2`, with two lower holes. Its actual
push attempt timed out in launcher worktree checkout after 600 seconds; the single retry
was killed with exit 137. Neither printed DELIVERED. The resumed attempt
`scratchpad/resumed-delivery.log` refused the then two-hole packet at 41 minutes of a
fresh reference clock. The clock changed from 2026-10-19 17:07:47 UTC to
2026-10-20 00:27:20 UTC (`.budget.start = 1792456040.1215837`). No budget or launcher
file was edited. Work continued and the integral hole was proved.

Earlier consumer validation compiled unchanged `A1FiniteEtaleWeilFibreComparison`,
`DlConstantFieldCharts` and `WeilOpenImageDelta` against the packet in 41.6, 22.3 and
13.9 seconds. The import-only compact-support adaptation compiled in 11.1 seconds;
the proved integral adjunction compiled in 4.7 seconds. The current seven-module build passed cleanly: identity 43.7 seconds, compact support
9.8 seconds, integral adjunction 6.3 seconds, coefficient statement 10.7 seconds,
common-stage identity 20.7 seconds, rational adjunction 24.0 seconds and assigned
module 26.2 seconds (`scratchpad/updated-seven-module-build.log`). The identity
helpers now locally respect transparency, avoiding expensive expansion of comparison
data. Delivery preflight results are recorded by the delivery tool.

## Forced adaptations

`Sheaf.Paper.SfIntegralCompactSupportConstructible`, held by K9: remove only
`import Sheaf.Paper.SfCommonStageDirectImage` (original line 47). Its declarations do not
reference the assigned module's declarations. The original file compiles alone, so this
is the launcher's explicitly supported import-only adaptation rather than a declaration
failure. The earlier combined-graph error is recorded verbatim in
`scratchpad/unique-family-dry-run.log`: `FAILED: import cycle`, traversing the assigned
module, rational adjunction, system realization, compact-support realization, finite
action, representative independence, integral/rational compact support, and the adapted
module back to the assigned module. The new route inserts the integral-adjunction module
before the system realization. Removing this edge makes the combined graph acyclic.
The adapted file compiles and every other byte agrees with the current source.

## New nodes

`lem-sf-coherent-rational-pullback-identity`: scalar-compatible rational identity,
proved in `Sheaf.Paper.CoherentRationalPullbackIdentity`.

`lem-sf-common-stage-pullback-identity`: identity descent on actual pair representatives,
proved in `Sheaf.Paper.CommonStagePullbackIdentity`.

`lem-sf-rational-direct-image-adjunctions`: finite rational adjunctions and their
normalized scalar mates, proved in `Sheaf.Paper.SfRationalDirectImageAdjunction` from
the proved integral input and the separate coefficient result.

`lem-sf-rational-direct-image-coefficient-compatibility`: independent normalized
coefficient-tower and finite-free mate theorem, one new hole. It uniquely fixes the left
stage family and asserts invertibility of mates for already specified adjunctions.
It asserts no pointwise existence, common-stage adjunction or Weil lifting.

`lem-sf-integral-pullback-linear-adjunction`: integral coefficient-linear constructible
adjunction before rationalization, now proved from actual system data and full restriction.

Change records: `coord/changes/E1-sf-adjunction-elaboration.md` and
`coord/changes/E1-sf-compact-support-import-cycle.md` record the definition-proof
elaboration changes and import-only adaptation, with users and current holders.

## Forced adaptations

### Sheaf.Paper.SfIntegralCompactSupportConstructible
Only imports removed (Sheaf.Paper.SfCommonStageDirectImage), e.g. to break an import cycle; nothing else changed. CODEX verifies that the removal is needed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
