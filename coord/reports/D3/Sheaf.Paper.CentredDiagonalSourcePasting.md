## What changed

Replaced the hole in `WeilConjectures.PurityFiniteSetting.centred_diagonal_source_pasting`
by the source-coordinate transport calculation. The statement and all its public imports
are unchanged. The proof identifies the composite difference map on each ordered coordinate
block, removes the centred open neighbourhoods by normalized section locality, uses the
existing second-input restriction theorem, and proves the site tensor/pullback naturality
and source-comparison cancellations explicitly.

Added proof imports of `SectionEtaleOpenCancellation`,
`NormalizedEtaleRestrictionComparison`, and `DifferenceSecondInputRestriction`.
The first two are new modules containing single, general interface lemmas. They do not
assume a composite chart, a ChartEquation, a purity orientation, or the desired pasting
conclusion. The existing second-input restriction theorem is used in its own module's
presentation and converted using the normalization agreement lemma, rather than restated.

Updated the assigned node's proof and proof dependencies to follow this argument.
The full assigned module compiled on the server in 29.2 seconds. Temporary profiler
options and the reported unused simplifier arguments were removed before delivery;
the delivery tool checks that final version again.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.centred_diagonal_source_pasting`
(node `lem-pur-centred-diagonal-source-pasting`).

Added these two holes, each as the whole proof of a public theorem in its own module:

- `WeilConjectures.PurityFiniteSetting.sectionEtaleRestriction_open_cancel`
  (`lem-pur-section-etale-open-cancellation`): cancellation of the common open restriction
  in a single section-locality comparison, for any Noetherian schemes and any normalized
  presentation N.
- `WeilConjectures.PurityFiniteSetting.normalizedE_eq_etaleRestriction`
  (`lem-pur-normalized-etale-restriction-comparison`): agreement of exceptional-compositor/rho
  locality with uniquely counit-normalized ambient locality, before applying sections.

This is a decomposition: one upper hole closed, two strictly smaller holes added, net -1.
The assigned module has no remaining sorry. No definitions or target signatures changed.
The new lemmas include empty schemes; the coordinate calculation uses Fin.addCases and
includes either zero block. No conclusion depends on a chosen orientation.

## No longer needed

No public imports were removed and no module is withdrawn or globally pruned.
The assigned proof no longer directly invokes
`lem-pur-affine-difference-tower-factorization` or
`lem-pur-dualizing-sigma-cocycle-locality`: the existing second-input restriction theorem
encapsulates that geometry and source-etale base-change calculation. They remain needed
by that theorem's argument and are not claimed as globally pruned.

The proof does not need the first-input or total-output tower identification theorems:
the first input is the full single-chart section comparison, the output map is identified
by its ordered generator formula, and the assumed ChartEquation already supplies pasting.
No import of `DifferenceCoordinateSectionIdentifications`, `DifferenceFirstInputRestriction`
as an independent proof dependency, or `NormalizedEtaleComparisonComposition` was added.
The first-input module remains a transitive import because it owns `normalizedE`.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The given proof plan's open cancellation and second-input base-change steps cross two
formal normalization presentations. The declarations supply all maps, but there was no
ready theorem equating those presentations. In particular, the centred source comparison
uses `tensorMateEtalePrecompLocalityIso` for N, whereas ChartEquation uses the unique
ambient counit-locality isomorphism, and the existing second-input theorem uses
`normalizedE`, defined through exceptional composition and rho. The two new statements
isolate these precise interface identities. Neither is the assigned pasting theorem
under another name.

No mathematical statement was disputed or weakened. No adopted-source declaration,
public import, or definition was changed, and no forced consumer adaptation was needed.

## New nodes

`lem-pur-section-etale-open-cancellation`, module
`Sheaf.Paper.SectionEtaleOpenCancellation`, formalizes proof Step 1's common-open
cancellation for arbitrary section-locality maps. Its source and full counit/pasting
argument are recorded in its docstring and node.

`lem-pur-normalized-etale-restriction-comparison`, module
`Sheaf.Paper.NormalizedEtaleRestrictionComparison`, formalizes agreement of the two
existing normalized exceptional-locality expressions before taking section pullbacks.
Its proof plan compares their identical adjunction counit transposes.

Both nodes inherit `sec-smooth-purity` / `sk-thm-smooth-purity`. Searches found only
abstract adjunction conjugacy and naturality in Mathlib; repository searches found the
existing maps and component equations, not these interface equalities. No change record
is needed: the delivery adds statements in new modules and changes only proofs/imports
of the assigned module.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
