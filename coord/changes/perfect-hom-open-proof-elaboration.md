## Reason

The categorical assembly needs CategoryTheory names in its private helpers and
must avoid unfolding the fixed right-derived-functor construction while checking
its final equality. These are local elaboration controls, not mathematical changes.

## Old

The existing module opens CategoryTheory only after its universe declarations and
has no local irreducibility declarations for the right-derived construction.

## New

An additional open command makes the names available to the three private helpers.
The local irreducibility attributes on Functor.rightDerivedFunctor,
Functor.rightDerivedFunctorUnit, and DerivedCategory.Qh prevent expensive unfolding
in the proof. Three private local instances restate the standard scheme module
instances only after both existing public definitions. Existing public signatures
and definition bodies are identical. The new imports are proof-only.

## Users

No downstream module mentions the interface scanner's command-change marker.
The open command and local attributes are confined to this file; the private local
instances are not exported. Importers retain the identical statements, definitions,
and public imports. No downstream adaptation is needed.

## Status

landed 20261014T052439-L-1913452 2026-10-14 (merge of deliver/H2/Sheaf.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization)
