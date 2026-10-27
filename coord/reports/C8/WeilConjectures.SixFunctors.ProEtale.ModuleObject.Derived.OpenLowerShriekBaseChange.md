## What changed

Filled the single proof hole in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange`.
The primed exchange has exactly the unit-square-counit formula accepted by the existing
component lemmas in `ExchangeMono` and `ExchangeSection`; both equality premises are `rfl`.
For each component, monicity and a section give the other inverse equation by cancellation.
`NatIso.isIso_of_isIso_app` then assembles invertibility of the natural transformation.
Added only private proof imports of those two modules. Every existing signature, attribute,
public import, docstring and non-theorem body stays unchanged. Updated the assigned route
node's proof, proof dependencies and proof origin to match the Lean proof.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange'`
(node `lem-route-is-iso-bounded-constructible-open-immersion-lower-shriek-base-change`).
No holes remain in the item and no holes or declarations were added elsewhere. This is a
proof from existing proved component statements, not a decomposition into new holes.
Server single-file compilation through `lcompile.py` passed with no errors or warnings
in 5.5 seconds. The delivery tool performs the final axiom and packet checks.

## No longer needed

No existing imports were removed; none were removable under the source-library boundary.
The provisional assigned node had no declared proof dependencies or steps to prune.
No modules or nodes are withdrawn. Directly importing the duplicate unprimed isomorphism
theorem from `BaseChangeTheorems.LowerShriek.MorphismDefs` would create an import cycle
through compactification independence and `OpenLowerShriekInterchange`; the proof instead
uses only the cycle-free component inputs `ExchangeMono` and `ExchangeSection`.
Both added imports are used directly: one supplies monicity, the other supplies the section.

## Where the brief, the DAG or earlier work was wrong

The assigned route node was provisional and unsplit, with no numbered proof steps or
proof dependencies. Its theorem nevertheless has an immediate proof from the two existing
component results for the identical formula. No new geometric theory is required here.
The unit record `sk-cor-existence-ii` has empty realization lists; this proof changes no
unit statement or prescribed unit step. The existing component results belong to the
open-base-change unit and supply exactly the needed geometric input without changing its
route. Identity and empty-open cases are covered by the same component lemmas; the
cartesian and open-immersion hypotheses are preserved and used in those lemmas.

A DAG-only dependency issue remains outside this packet: the component nodes cite the broad
`sk-def-sfb-dc-restricted-functors` definition, whose statement dependencies include lower-star
preservation, proper constructible cohomology, and `def-sfb-derived-open-lower-shriek-id`,
which reaches this provisional route node. Thus adding the actual component dependencies
exposes a cycle in that coarse DAG metadata. It is not a Lean import or proof cycle:
`import_direction.py may` accepts `ExchangeSection` (and its `ExchangeMono` dependency),
whose implementations depend only on the bounded-constructible functors, ordinary open
base change and recollement. The forbidden downstream unprimed theorem is not imported.
This delivery records the actual proof dependencies and leaves the unrelated definition
nodes and their overly broad attachments for the maintainer to reconcile.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
