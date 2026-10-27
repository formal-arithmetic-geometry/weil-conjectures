## What changed

Filled `CategoryTheory.Endofunctor.IsoAlgebra.exists_cyclicDerivedActionRealization`
without changing its signature. Private proved helpers lift the prescribed action to a
K-injective complex, construct the inverse-iterate sequential colimit, prove its initial
leg is a quasi-isomorphism, build its invertible chain action and fixed-pair complex,
and identify the canonical localized structure map. Exact faithful forgetting transports
all cohomology intervals and isomorphism-invariant object properties.

The sequential-colimit argument follows the existing DAG, with a shorter construction
of its structure isomorphism: first construct `C ≅ R(C)`, then apply the equivalence
and its counit. Updated the node proof and dependency list accordingly.

Added local registrations of the existing composition-preservation instances. The
static interface scan requested a change record for this command; see
`coord/changes/G5-cyclic-derived-local-instances.md`. It affects proof elaboration
inside this module. The downstream check reports no current Lean importers.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.Endofunctor.IsoAlgebra.exists_cyclicDerivedActionRealization`
(node `lem-sf-cyclic-derived-action-realization`). One original hole, zero remaining
holes, zero holes added, zero split off. All helpers have complete proofs. No data
is extracted from a mere existence theorem with an unproved body: the colimit and
fixed-pair complex are constructed explicitly. K-injective resolutions and the
localization API are the existing library declarations.

The final module compiled cleanly in 11.1 seconds. The axiom check for the theorem
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. Its signature is
verbatim unchanged and every Lean line has at most 100 characters.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`:
exactness and faithfulness of forgetting already hold in the source IsoAlgebra library.
The node `lem-sf-fixed-pair-derived-forget-comparison` and its corresponding module
are unnecessary for this proof; its obsolete `tool_uses` entry is removed. This does
not assert that other consumers no longer need that module.

Removed redundant direct proof imports
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
`Mathlib.CategoryTheory.Limits.HasLimits`, whose APIs are provided by retained imports.
All other declared mathematical dependencies are retained. No modules withdrawn.

## Where the brief, the DAG or earlier work was wrong

The mathematical sequential-colimit plan is valid. Its right-derived-forgetting
comparison dependency is stronger than needed: exact faithful forgetting suffices.
Boundedness is not needed by the construction, though its original binder is preserved.
The fixed-pair Grothendieck hypothesis is likewise unnecessary for the constructed
complex. No target, definition or theorem signature changed; no forced adaptations.

Initial compile-service requests repeatedly returned exit code 124 without Lean
feedback. Work continued in the original sandbox until compiler feedback became
available. These service failures are not counted as compile tests.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
