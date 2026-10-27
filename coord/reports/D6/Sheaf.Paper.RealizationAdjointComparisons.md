## What changed

Proved `WeilConjectures.realization_adjoint_comparisons` from the existing scalar
restriction normalization theorem and the proved abstract scalar-normalized
adjunction square. The proof handles the arbitrary supplied push datum using its
own transpose normalization, identifies its coefficient isomorphisms by their
normalizations, restricts the actual ambient adjunction, and transports it along
the actual strict completion unit. The raw rational adjunction is constructed
with Mathlib's localization adjunction for the specified tensor transports.
The comparison isomorphisms descend through fully faithful precomposition and
retain exactly the displayed conjugated integral components.

The complete item module compiles cleanly through `lcompile.py` (20.1 s), with no
errors or warnings. The private generic localization and comparison helpers also
compiled separately during development (6.4 s).
All new helpers are private and proved in the item module. Existing public
signatures and definitions are unchanged. Updated the item's DAG proof and
proof dependencies to match this argument. No new theorem module is introduced. The module-command elaboration changes
are documented in `coord/changes/D6-realization-adjoint-proof-context.md`; no
consumer needs adaptation. The first preflight requested this record for the
private helper section and local unfolding wrapper.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.realization_adjoint_comparisons`
(node `lem-weil-pbc-realization-adjoint-comparisons`). Added zero holes. No
`sorry` remains in the delivered module. The imported existing
`WeilConjectures.realization_restriction_normalizations` remains a stated proof
dependency; this delivery does not claim to prove that separate item.

## No longer needed

Removed the redundant private imports `Mathlib.CategoryTheory.Adjunction.Mates`,
`Sheaf.CategoryTheory.LocalizationInverseImageCoherence`, and
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`; the existing public
interfaces and the normalization/square dependencies already provide the declarations
used here. No public import was changed.

The proof does not use `lem-weil-pbc-completed-localized-adjunction-square`
(`Sheaf.CategoryTheory.CompletedLocalizedAdjunctionSquare`). Its existential
localized functors would require additional identifications with the functors
specified here. Instead the proof applies `Adjunction.ofNatIsoLeft` and Mathlib's
`Adjunction.localization` directly to the actual functors, using the already
proved raw-localization helpers in
`Sheaf.Paper.RealizationPullRationalDescent`. Removed that node from this item's
proof dependencies. No module is withdrawn: other consumers may still need it.

## Where the brief, the DAG or earlier work was wrong

The existing plan's coefficient-normalization theorem supplies a push datum
existentially, whereas this item quantifies over an arbitrary supplied push datum.
Only its pull and ambient counit clauses are required; the supplied push datum's
own `beta_normalization` gives the missing equation directly. Thus no equality
of complete push-data records and no equality of their auxiliary witnesses is
needed. The planned completion/localization theorem constructs existential raw
functors; the direct Mathlib localization route fixes the actual tensor functors
from the outset. The theorem statement and unit route are unchanged.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
