## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_adjunction_localization`
with its complete original signature. All existing public imports are preserved.
Added proof imports for the existing linearization full-faithfulness API and detection
of shift compatibility after precomposition. The derived adjunction is the Mathlib
localization of the actual termwise adjunction, using the canonical factorization
isomorphisms. Both requested normalization equations are proved explicitly.

Four proved private helpers establish the actual open unit isomorphism, descent of
unit invertibility, descent of integer-shift compatibility, and the shifted Hom formula.
They add no assumptions to the public theorem. Updated the node proof to the actual
six-step argument and the theorem proof description accordingly.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_adjunction_localization`
(node `lem-sfb-condensed-open-adjunction-localization`). Added 0 holes; split off 0.
No `sorry` remains in the delivered Lean file. The four private helpers are fully proved.
The single-file compiler accepted the complete argument; delivery preflight performs
its independent compilation and axiom checks. Existing dependencies may retain their
own holes, including the abelian geometric inputs; no global closure claim is made.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`: the original upstream functors
  already expose their additivity and exactness instances; the extra bundled theorem
  is unnecessary. The corresponding node remains a dependency for these mathematical
  properties, but its separate module need not be imported here.
- `Sheaf.CategoryTheory.SheafTensor`: no sheaf-tensor theorem is used; the existing
  upstream sheaf and module instances supply the requisite structures. Removed
  `sk-def-sfb-sheaf-tensor` from this node's direct proof dependencies.
- `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`,
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
  `WeilConjectures.CategoryTheory.ModuleObjects.Abelian`, and
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`: redundant direct proof
  imports; the retained public interfaces and linearization API already expose what
  the proof needs. Their underlying mathematical dependencies are retained where used.
- `Mathlib.CategoryTheory.Localization.Predicate`: redundant direct import, supplied
  by `Mathlib.CategoryTheory.Localization.Adjunction`.

The direct node dependencies `def-weil-pbc-composite-adjunction` and
`sk-def-sfb-change-of-scalars` are no longer needed as separate proof steps: full
faithfulness of the actual composite left adjoint proves invertibility of the unit
for its specified adjunction, without expanding the composite unit. The existing
`def-sfb-modobj-restriction-equivalence` states exactly the restriction equivalence
used and replaces the broader change-of-scalars dependency.
No module is withdrawn; no claim is made that these dependencies are globally unused.
The unit route of `sk-thm-sf-comp-composition` is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan described a longer calculation of the actual composite module unit.
The existing proved `Adjunction.fullyFaithfulMapModLeft` and
`Mod.comapEquivalenceOfIsIso`, followed by Mathlib's fully faithful left-adjoint unit
criterion, already give the required unit for the specified adjunction. No statement,
definition, target, or consumer is changed. No forced adaptations or new nodes.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
