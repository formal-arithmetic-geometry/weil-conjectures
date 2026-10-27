## What changed

Filled `AlgebraicGeometry.Etale.properSupportPullbackSectionMap` in
`Sheaf.SecSmoothPurity.ProperSupportPullbackSectionMap`, retaining the original public
signatures, definitions and docstrings. Added proved private helpers for the ModuleCat
unit/germ comparison, naturality of the Cartesian lift, proper-support preservation,
and lifting a linear sheaf map through a monomorphism.

The support proof uses `sectionHasProperSupport_iff`,
`closed_proper_support_locality`, and `proper_iso_image`. The final coefficient square
uses naturality of the adjunction unit and cancellation of the target inclusion.
Updated the existing node's proof and dependencies to describe this implementation.
The proof-local namespace and elaboration commands and import changes are recorded in
`coord/changes/proper-support-pullback-proof-imports.md`; no consumer is adapted.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.properSupportPullbackSectionMap`
(node `lem-cbc-proper-support-pullback-section-map`).
No holes added, no split-off statements, and no `sorry` remains in the delivered module.
All added private lemmas have complete proofs.
Validation: `lcompile.py` compiled the completed module cleanly in 24.5 seconds. The explicit projection API and local
irreducibility of the Cartesian definitions avoid a unification heartbeat failure;
the definitions and their exported attributes are unchanged.

## No longer needed

Removed direct proof imports:
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`;
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`;
- `Sheaf.EtaleCohomology.EtaleSectionZeroOpen`;
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already available through
  the retained public support import).

The specialized abelian stalk/germ theorem and module-transport proposition are replaced
by a direct ModuleCat proof using the existing stalk isomorphism and abstract adjunction.
The zero-open and closed-subset properness results are still needed transitively through
the closed-support and proper-support locality APIs; their modules are not withdrawn.
The proof no longer needs the separate nodes
`lem-weil-pbc-inverse-image-stalk-germ`,
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-sc-etale-section-zero-open`, or
`lem-weil-pbc-closed-subset-proper-over-base-properties` as direct dependencies.
Removed the obsolete top-level tool approvals for the first two and the last of these,
keeping the local-finite-type base-change approval in its original order.
No module is withdrawn; no adopted source declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The original final proof step unnecessarily constructs coefficient maps gamma and delta.
The Lean theorem already takes these maps, their compatibility with inclusions, and the
second pullback map as hypotheses. It therefore suffices to prove the ambient coefficient
square and cancel the target inclusion. The source-library signatures and the unit route
are preserved.

The recorded abelian inverse-image germ theorem is stated for algebraically closed
points, while this theorem tests all separably closed points and uses ModuleCat. The
existing general-coefficient stalk isomorphism supports the direct unit/germ calculation
with precisely these coefficients and points. The first private germ helpers follow the
proved calculations in `ProperSupportFibreRestrictionCompatibility`; that module imports
this item, so importing it here would create a cycle.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
