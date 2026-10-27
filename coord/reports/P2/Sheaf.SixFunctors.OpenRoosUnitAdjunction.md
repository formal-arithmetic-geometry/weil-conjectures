## What changed

Replaced the proof hole in `WeilConjectures.OpenRoos.openRoosUnitAdjunction` by an assembly of the coefficient arithmetic, actual quotient-unit reflector, normalized restriction comparison, completeness preservation, and the restricted full-subcategory adjunction. The existing public statements and definitions are unchanged. Added proved private helpers for the arithmetic, Hom-bijection transport, principal-cone reflector, subterminal ordinary unit, derived unit formula, and restricted adjunction.

Added `Sheaf.SixFunctors.OpenRoosRestrictionDescent` for the separate comparison between the normalized strict quotient tower and the published `IntegralOnSlice` completion. It supplies the all-object unit square and the representative equation with the specified `scalarRoosMap`. The parent proves uniqueness from the reflector Hom injection and performs the remaining assembly itself. Updated the parent DAG proof and dependencies to match this route.

## Proved and sorry left

Closed the original hole in `WeilConjectures.OpenRoos.openRoosUnitAdjunction` (node `lem-sf-open-roos-unit-adjunction`), conditional on the stated dependencies.

Added one hole: `WeilConjectures.OpenRoosRestriction.restrictionDescent` (node `lem-sf-open-roos-restriction-descent`). Its module has one named theorem with source and a complete proof in words. This is a decomposition of one original hole into one strictly narrower model-comparison result, not a net hole reduction. The item module has zero direct `sorry` tokens; the added module has one. Existing imported theorem holes are retained.

The complete item and the new restriction-descent module compile through `lcompile.py`. Large existential witnesses are shared using explicit projections, and the unit-comparison uniqueness argument is proved for abstract functors before specialization. Some runs hit the fixed compile limit under load; successful complete checks returned exit code zero. The item contains no direct proof holes; its coefficient, reflector, uniqueness, and adjunction arguments are complete. The retained restriction-descent theorem is the one new hole described above.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.CompletedKoszulQuotientComparison`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.ExactProductFunctorStrictLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts`
- `Sheaf.SixFunctors.OpenSemilinearTensorModel`

The parent no longer directly uses `lem-sf-quotient-completion-actual-reflector`: its same-universe transported presentation is replaced by the existing independent-universe principal-cone results and the Koszul reflector. It also no longer directly uses `lem-sf-immersion-completed-pullback-comparison`: the chosen integral-open comparison supplies completeness preservation. These nodes may still be needed elsewhere and no module is withdrawn.

The old direct dependencies `lem-weil-proetale-weakly-etale-localization`, `lem-weil-pbc-profinite-coefficient-inverse-image`, `lem-weil-pbc-proetale-immersion-limit-preservation`, and `lem-sf-open-quotient-completion-unit-comparison` remain in the proof plan of the new restriction-descent node. They are relocated dependencies, not globally pruned mathematics.

## Where the brief, the DAG or earlier work was wrong

The former Step 4 asks for a reflector whose attached theorem has only one shared site/coefficient universe, whereas this item's statement has independent universes. The existing principal-cone and small-model interfaces provide the needed route without changing any statement.

The strict quotient completion of `OpenQuotientCompletionUnitComparison` and the published `IntegralOnSlice.completion` are different constructions. The former theorem existentially supplies its own normalized Operations, while the item must use the Operations chosen by the integral-open completeness comparison. Descent and transport to that prescribed Operations, with the actual unit and signed Roos normalization, are substantive glue; they are isolated in the new result rather than silently identified definitionally.

The open object is subterminal even when empty, so the ordinary extension/restriction unit is already invertible before restricting to complete objects. Mathlib's `Adjunction.restrictFullyFaithful` then gives both required restricted component equations and full faithfulness.

## New nodes

`lem-sf-open-roos-restriction-descent`, at `dag/nodes/sec-six-functors/lem-sf-open-roos-restriction-descent.json`, formalizes the normalized restriction/completion model descent from the source argument (Stacks 099N (2),(5), 0941, 0G7E and 07A4). Its statement excludes arithmetic, reflection, completeness preservation, uniqueness, extension, and the restricted adjunction. Edge cases checked in the source argument include the empty open and zero complexes; the construction is by coefficient normalization, strict tensors, products, and fully faithful localization, with no completeness or boundedness hypothesis.

No change record is required: no existing public signature or definition is changed, and no other module is adapted.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
