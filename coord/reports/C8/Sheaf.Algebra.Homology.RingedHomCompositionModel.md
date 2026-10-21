## What changed

Proved CategoryTheory.ringedHomComposition_naturality in
Sheaf.Algebra.Homology.RingedHomCompositionModel. Its three components are
contravariant naturality in the first variable, covariant naturality in the
last variable, and dinaturality in the middle variable. Private helpers derive
inverse-transpose formulas from the given closed adjunction and its counit.
Naturality of the associator and tensor interchange identify the uncurried
maps; injectivity of inverse transposition proves each equation.

All public signatures, definitions, attributes and imports are unchanged.
The added helpers are private and proved. The monoidal namespace is opened
only for the private naturality helper; the corresponding conservative
interface-check change is recorded in coord/changes/. The proof follows steps 1 and 2 of
lem-sfb-ringed-hom-composition-model, so no DAG change is required. No module
outside the assigned item is changed. The unit route is unchanged.

## Proved and sorry left

Closed 1 of the original 3 holes:
CategoryTheory.ringedHomComposition_naturality.

The following original holes remain, both attached to
lem-sfb-ringed-hom-composition-model:

- CategoryTheory.ringedHomComposition_existsUnique.
- CategoryTheory.ringedHomComposition_model.

The delivered module therefore contains 2 sorry occurrences. No holes are added
and no result is split off. The constructive graded-map and derived-model
attempts remain outside the delivery in sandbox diagnostic text files; they
are not claimed as proved.

## No longer needed

None. No import, node or module is pruned. The original existence and model
proof plans and their dependencies remain needed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or route correction. Steps 1 and 2 reduce directly to
the counit naturality identities in the supplied closed structure. The
construction and representative comparison in steps 3 through 8 remain open.

Delivery status: the initial preflight requested a change record for the added
namespace opening. The opening is now scoped to the private helper and the
record now has all five required sections and a table of the downstream consumer.
The current retained module compiled successfully (exit code 0, 6.5 seconds).
The resumed preflight identified only the incomplete change-record structure and
its missing explicit report path; both are repaired. The record is
coord/changes/ringed-hom-composition-private-naturality.md. Earlier exit-143
delivery failures belong to the previous attempt; the current delivery tool
reached server preflight and returned actionable metadata diagnostics.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
