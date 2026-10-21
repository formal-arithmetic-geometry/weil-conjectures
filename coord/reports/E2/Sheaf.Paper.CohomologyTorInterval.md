## What changed

Completed `AlgebraicGeometry.ProEtale.torAmplitudeIn_of_cohomology_interval` in
`Sheaf.Paper.CohomologyTorInterval`, preserving its complete statement, universes,
visibility and public imports. The proof uses the already proved source-library
`DerivedCategory.prop_of_isGE_of_isLE_of_degreewise` to perform the blueprint's finite
truncation induction. For its degreewise input, it commutes the actual relative derived
tensor with the integer shift `-q`, moves the two t-structure bounds, and enlarges
`[q+c,q+d]` to `[a+c,b+d]`. The zero case follows from additivity of the tensor functor;
extension closure comes from the stated and proved
`constantModelConstructibleFiniteTor_wellDefined`.

Added private proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
Updated the item's proof steps and dependencies. Added a DAG attachment for the existing
proved degreewise dévissage theorem; no new Lean declarations or assumptions are introduced.
The unit's Complexes route through finite truncation induction and common-interval
extension stability is retained.

Validation: the final Lean file compiled through `lcompile.py` without errors or warnings
in 21.9 seconds. Both added proof imports pass `import_direction.py may`. The theorem
covers zero complexes, a one-degree interval, and negative cohomological degrees without
any case-specific assumption. The generic dévissage lemma also handles an empty interval
by the disjoint t-structure bounds. All changed Lean lines are at most 100 characters.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.torAmplitudeIn_of_cohomology_interval`
(node `lem-sfb-cohomology-tor-interval`), the item's only original hole.

Actual hole count in the delivered Lean module: 1 before, 0 after. Holes added: 0.
Split-off theorems: 0. No `sorry` remains in any delivered Lean file.
The new node records an existing complete proof and adds no proof obligation.

## No longer needed

Removed four proof-only imports from this module:

- `Sheaf.CategoryTheory.RingedSiteModules`: the theorem already uses the actual internal
  module category and its existing abelian/derived instances, without a sectionwise
  module-category comparison.
- `Sheaf.CategoryTheory.TruncationDescends`: the proved degreewise dévissage handles the
  canonical derived truncations internally.
- `WeilConjectures.CategoryTheory.TruncationTriangle`: the same existing dévissage uses
  Mathlib's standard t-structure truncation triangle; no separate successive-truncation
  construction is required here.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: no derived Hom or
  tensor/Hom adjunction is used. The needed relative tensor structures already come from
  the unchanged public import closure; its shift API is imported directly.

Removed direct proof dependencies and their obsolete top-level tool approvals:
`def-weil-sheaf-of-modules-category`, `lem-weil-pbc-truncation-descends`, and
`lem-weil-pbc-truncation-triangle`. The relative derived tensor dependency
`sk-def-sfb-derived-tensor-hom` remains: its tensor structures and K-flat shift machinery
are used even though its broad Hom module need not be imported directly.

These are removals from this item's proof, not withdrawals of the modules or of their
other consumers. No source-library declaration is removed or altered. No whole-library
module is claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's explicit reconstruction of truncation endpoints
and the finite tower was unnecessary: the source library already proves the exact generic
degreewise dévissage needed here. A fixed Tor interval is not shift-stable, so the ordinary
triangulated-subcategory dévissage would not suffice; the degreewise version requires only
zero objects, isomorphism invariance and extensions.

## New nodes

`lem-sfb-degreewise-bounded-devissage` attaches the existing source theorem
`DerivedCategory.prop_of_isGE_of_isLE_of_degreewise` in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`. Its full generic
statement and finite-truncation proof are recorded, with Stacks Tag 08J5 and the blueprint's
Complexes paragraph as sources. LeanSearch, Loogle, Mathlib/source/DAG grep and blueprint
search found no Mathlib theorem or existing exact node. The Lean implementation already
exists and is unchanged. This node is a reusable proof input, not a split-off hole.
No change record is needed: no signature, public import, definition, attribute or
module-level elaboration command changes.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
