## What changed

Filled the nine theorem holes in `Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector`.
The proof uses the existing ordinary clopen comparison and unit, the canonical
exact/right-derived comparison, and adjunction mates. Private helpers verify the
localization normalization and derive the four naturality squares from the two
unit equations. No public signature or definition changed. No other Lean module
is modified.

The additional proof imports expose existing helpers in VaryingRingOperations
and VaryingRingModulePiComplementZero. The last supplies
vanishing of extension restricted to a disjoint open. The node proof records the
actual localization and iterated-mates route. The static interface check requires
a record for the added local attributes and private-helper section:
`coord/changes/semilinear-clopen-proof-local-attributes.md`. All attributes are local;
the downstream query reports zero current Lean consumers.

## Proved and sorry left

Closed the nine original holes: `semilinearClopen_openUnit_isIso`,
`semilinearClopen_push_colimits`, `semilinearClopen_unit_projector`,
`clopenCoefficientMap_commute`, `clopenCoefficientPush_existsUnique`,
`clopenCoefficientPullInv_isIso`, `clopenCoefficientJInv_isIso`,
`clopenCoefficientP_isIso`, and `semilinearClopen_coefficient_naturality`.
All belong to `lem-sf-semilinear-clopen-unit-projector`.

Holes remaining in the item: zero. Holes added: zero. Split-off statements: zero.
The dependency theorems are used with their existing proofs; no new assumptions
or axioms are introduced.

The full module compiled cleanly on the project server (57.8 seconds, exit 0),
with no warnings. All 26 public signatures and every existing definition match the
shared source. Diagnostic prefixes are under scratchpad and are not new library
modules. The delivery tool performs the remaining consumer, node and axiom checks.

## No longer needed

Removed proof imports `Sheaf.SixFunctors.OpenTensorNormalizationData`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`, `Sheaf.CategoryTheory.RingedSiteModules`,
and `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.

The item's proof no longer directly needs nodes `def-weil-exact-derived-adjunction`,
`def-weil-pbc-proetale-site`, `def-weil-pbc-sites-and-cohomology`,
`def-weil-sheaf-of-modules-category`, or
`lem-weil-pbc-exact-functor-derived-functor`. The existing ordinary operations
already implement the sheaf calculations, and Mathlib's canonical exact-derived
comparison and its unit factorization give the required normalization directly.
The full VaryingRingProperOpenPasting module is also unnecessary: its narrower,
already-proved complementary-component module supplies exactly the zero-target
calculation used here. The arrow module needs only its public interface; no
private arrow proofs are imported.

These modules may still be needed by other consumers; none is withdrawn here.

A separate componentwise K-flat tensor calculation is unnecessary. The given
scalar adjunctions, iterated mates, and preservation of inverses by conjugation
give the actual specified scalar comparison equations, without additional
flatness or boundedness hypotheses. No declared dependency needed by an existing
upstream proof is removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned direct section/tensor calculation
can be shortened using already-proved ordinary clopen operations and categorical
mate identities. The proof dependency on VaryingRingModulePiComplementZero is acyclic;
its disjoint-extension helper gives the complementary zero target.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
