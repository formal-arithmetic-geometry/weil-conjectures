## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.derivedDirectImageAssociativity`
without changing its signature or any definition. The proof specializes the already
proved generic `Functor.rightDerivedFunctorCompIso'_assoc` to the actual module
pushforwards and uses the already proved `lowerStarComp_assoc`. It accounts for the
scheme associativity transport, derives its composition equation, and inverts and
cancels the resulting isomorphisms. All added imports are private proof imports.
Updated the item's DAG proof and proof dependencies to this shorter route.
Server single-file compilation passed cleanly in 9.0 seconds.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.derivedDirectImageAssociativity`
(node `lem-sfb-derived-direct-image-associativity`). One of one holes closed;
zero holes added, zero split off, zero holes remain in this delivery.

## No longer needed

The item's proof does not need `lem-sfb-kinjective-direct-image-open-word-model`
(`Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel`) or
`lem-sfb-module-direct-image-open-pasting`
(`Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting`). Their general word descent
and open-slice pasting assertions are replaced here by the proved generic derived
composition associativity law and the existing ordinary module compositor coherence.
These were DAG proof dependencies, not imports of the original item module; no existing
import was removed and no module was withdrawn. Other consumers may still need them.
The original public import of the coherence data stays necessary for the statement.
No unit statement or realized step was removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's word-descent route is valid but unnecessarily general for pure direct-image
associativity. The source library already provides the required generic associativity
law. `module_derived_compositor_coherence` in a related module follows that route but
its public signature imposes admissibility; the present proof applies the generic law
directly and therefore preserves this item's unrestricted coefficient statement.
No definition repair, source-library edit, new statement, or forced adaptation was needed.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
