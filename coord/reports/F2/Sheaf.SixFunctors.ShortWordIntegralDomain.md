## What changed

Replaced the proof of `WeilConjectures.GeneratorReduction.shortWordIntegralDomain` in
`Sheaf.SixFunctors.ShortWordIntegralDomain` by structural induction, with private helpers.
All existing public signatures, definitions, options and public imports are preserved.
Added private proof imports of `PurNormalizedReconstructionAdjunctionCalculus`,
`SfDerivedCompleteLegacyComparison`, `ProEtaleBoundedConstructibleTriangulated`, and
`OpenReconstructionEffectivity` (the last with `import all`, reusing its proved private
`complete_of_iso` and `tensorUnit_complete`). No dependency module is edited.

The induction constructs an isomorphism between the actual integral evaluation and the
actual total limit of the system evaluation. At tensor and pullback vertices it uses the
fixed quotient-tower comparisons; proper image is already the appropriate limit. At open
vertices it uses the inverse actual reduction mate and the actual reconstruction unit.
Normalized reconstruction gives completeness and the effective counit. Finite evaluation
then transports intrinsic constructibility, the common cohomological interval, and the
common Tor interval. Tor transport just composes the representative isomorphism appearing
in the definition of `HasProEtaleTorAmplitude`; it requires no new preservation theorem.

The required Mathlib searches were made before writing the proof: LeanFinder for
normalized tower total limits, derived completeness, bounded constructibility and finite
Tor amplitude returned generic ordinary adic-completion and categorical-limit results;
Loogle `IsIso, CategoryTheory.Iso` returned no match (unqualified `IsIso` was unknown),
and the msearch grep for `finiteTorConstructibleIntegral|NormalizedDvrTower` returned none.
Local searches of both library roots found the existing reconstruction and comparison
interfaces used here, so no new mathematical statement was needed.

Updated the existing item's DAG proof, proof dependencies and proof origin to describe
these steps and the declarations actually used. No new nodes or change records.

Validation: the final module compiled through the required remote `lcompile.py` in
4.6 seconds with no errors or warnings. All Lean lines have at most 100 characters.
Only `proof`, `proof_deps` and `proof_origin` changed in the existing node.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.GeneratorReduction.shortWordIntegralDomain`
(node `lem-sf-short-word-integral-domain`). Added zero holes; zero holes remain in the
item or elsewhere in this delivery. All private helpers have complete proofs/constructions.
Existing imported theorem holes are used as the project's stated dependencies, not copied
or restated. This is a proof of the assigned statement, not a decomposition.

## No longer needed

No original Lean import was removed: the only original import,
`Sheaf.SixFunctors.GeneratorReductionData`, remains necessary for the statement.
No Lean module or declaration is withdrawn, and no whole module is claimed pruned.

The following old direct proof dependencies are omitted from the revised route:

- `lem-sf-integral-basic-realization` (`Sheaf.SixFunctors.IntegralBasicRealization`):
  the concrete global tensor/pullback comparisons already give the needed realization,
  and proper image is a limit by definition. The abstract primitive-realization package
  and its finite-field hypotheses are unnecessary here.
- `lem-sf-integral-open-reduction-comparison`
  (`Sheaf.SixFunctors.IntegralOpenReductionComparison`): use the specified realization
  model's open mate and `openReconstructionEffectivity` directly.
- `lem-coef-normalized-dvr-effectivity` (`Sheaf.Paper.NormalizedDVREffectivity`):
  use the existing unrestricted reconstruction theorem as the direct interface.
  DVR effectivity remains an indirect dependency of that theorem.
- `def-pur-integral-derived-operations`
  (`Sheaf.Paper.IntegralDerivedOperationsOnSlices`): no slice-level construction is
  used directly; the existing global quotient-tower comparisons are sufficient.
  The operations and their supporting modules remain indirect dependencies.

The old open-reduction package may likewise remain indirectly reachable. These are direct
proof-plan simplifications, not claims that their entire library modules become unreachable.

## Where the brief, the DAG or earlier work was wrong

No statement error or definition repair was needed. The recorded plan's normalized-limit
argument is valid, but the existing unrestricted reconstruction theorem is a more useful
interface than the raw DVR effectivity theorem. `integralBasicRealization` also has an
auxiliary finite-field datum and geometric hypotheses absent from this item's signature;
the concrete global quotient-tower comparisons avoid that interface mismatch.

The length restriction is unnecessary inside the proof: recursive admissibility supplies
all the required bounds and normalization at every vertex of any finite word. The public
statement keeps its original length-at-most-two hypothesis unchanged. The proof constructs
membership even for the scalar-unit case by transporting the given unit-system bounds.
Identity maps, empty opens, zero inputs, empty input families and degenerate ordered
intervals are handled by the same constructions; no additional hypotheses are introduced.
The unit's published route and all unit records remain unchanged.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
