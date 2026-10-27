## What changed

Simplified the two supported compactness assemblies in
`Sheaf.SixFunctorsBasics.BrownHypotheses` and removed its proof import of
`Sheaf.SixFunctorsBasics.BrownHypothesesArbitraryFieldCompactness`.

`CategoryTheory.brownHypotheses_of_finiteFieldDatum` now chooses one small skeleton
from admissible-coefficient smallness, applies
`CategoryTheory.brownHypothesesFiniteFieldCompactness` to those representatives, and
uses `CategoryTheory.brownHypothesesFor_iff_compact_representatives` directly. This
avoids the intervening objectwise theorem and its subsequent transport back to an
arbitrary object. The finite-field datum and all six coefficient cases are retained.

The reverse implication of
`CategoryTheory.brownHypothesesFor_padicIntegers_iff_ext_bounded` now applies
`AlgebraicGeometry.ProEtale.integralConstructibleCompactness` directly. It rewrites
the resulting coproduct-and-compactness witness along the already proved equality
of the localizing closures. It needs neither a separately chosen coproduct witness
nor a second objectwise compactness theorem. Every Ext bound remains explicit.

The private `CategoryTheory.brownHypotheses_admissible_small` helper now accepts the
actual `IsLocalizingAdmissibleCoefficient` predicate, avoiding the duplicated
reordered disjunction in its signature and caller. All public declarations,
definition bodies, instances, attributes and public imports are unchanged.
The delivery's interface checker reports no public interface changes. Its only
changed signature is that private proof helper; it has no external source uses.
The direct importers, `Sheaf.Paper.LocalizingExceptionalAdjoint` and
`Sheaf.Paper.ExceptionalInverseImageExistence`, require no adaptation.

The two changed proof nodes follow these direct assemblies. Change record:
`coord/changes/G4-brown-representative-compactness-pruning.md`.

Validation: `lcompile.py` compiled the revised proof bodies cleanly in 44.0 seconds
(exit code 0), within the 60-second limit. The profiled original took 53.8 seconds.
Development profiler options were removed before validation. Final source also
contains the updated proof docstrings; delivery checks compile that exact packet.

## Proved and sorry left

Holes closed: none (0 of 1). Holes added: none. Split-off statements: none.
The sole remaining hole is `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`. Its existing statement, signature and
`STATEMENT-DISPUTED` notice remain unchanged. No false compactness statement is
introduced or used to discharge it. The two valid theorems named above have
complete replacement proofs; all previously proved declarations remain proved.
This delivery prunes a proof dependency, rather than claiming a proof or a
decomposition of the disputed arbitrary-field assertion.

## No longer needed

Removed proof import and module from the item's import closure:
`Sheaf.SixFunctorsBasics.BrownHypothesesArbitraryFieldCompactness`.
A source-import graph comparison finds exactly this module removed and no module
newly reached. Both of its declarations are bypassed:

- `CategoryTheory.brownHypotheses_finiteField_object_compactness`, node
  `p3-brown-finite-field-object-compactness`: use compact representatives and their
  existing Brown criterion directly.
- `CategoryTheory.brownHypotheses_integral_object_compactness_of_ext_bounded`, node
  `p3-brown-integral-object-compactness-with-ext-bound`: rewrite the original
  integral compactness witness directly along the closure equality.

The changed parent nodes remove their proof edges to these nodes. A scan of all
node statements' dependency fields and proof-step uses found no other parents of
these two nodes. Their files and Lean attachments are preserved; no quarantined
module or source-library declaration is withdrawn. Their underlying finite,
rational and integral compactness inputs remain needed, as does the unit's route.
The replacement proof imports are
`Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` and
`Sheaf.Paper.IntegralConstructibleCompactness`.

## Where the brief, the DAG or earlier work was wrong

The sole hole cannot be proved from the available valid inputs: its existing
arbitrary-field statement is disputed, with the missing cohomological-dimension
hypothesis and infinite-transcendence-degree obstruction already recorded in the
module and node. The current blueprint still carries the unrestricted assertion.
The valid finite-field specialization and the integral criterion with explicit
Ext bounds are kept distinct. No weakened theorem replaces the original claim.

The rework table still lists a quarantine path, but the module was already
restored in the current shared source by the preceding G1 delivery. This packet
changes its actual proof route; it is neither a restoration no-op nor a rebase.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
