## What changed

Proved `WeilConjectures.scalarOrdinaryTensorChain_existsUnique`, preserving its
statement and every existing definition. Existence specializes the existing
normalized chain tensor comparison to the completed coefficient map, identifying
its ordinary extension with `integralOrdinaryScalar` by the object/map equations.
The sheafification-unit formula identifies the prescribed scalar sections.
Uniqueness transposes through the ordinary scalar adjunction and uses the existing
extensionality lemma for total pure tensor generators.

Added private proof imports of `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData`
and `Sheaf.Algebra.Homology.ScalarHomTensorCoherence`. The existing
`IntegralScalarExtension` proof import now exposes its private object/map API.

To meet the compile limit, the coefficient sheaves, ordinary scalar functor,
scalar sections and total tensor functor are locally irreducible; the tower and
Roos functors become irreducible after their construction. Elaboration respects
transparency throughout the module. The existing `scalarGood` proof uses its
object/map API, and three generic Roos steps explicitly unfold their small
expressions. The completeness proof uses the actual global site and coefficient
sheaf instead of their option-indexed aliases, with explicit universes for the
forgetful functor. Necessary reductions occur in individual proof steps. A local
priority selects Mathlib's existing sheaf-composition instance from preservation
of limits. No new declaration, data construction or mathematical assumption is
introduced by these elaboration repairs.

## Proved and sorry left

Closed one of the ten holes in the current shared source:
`WeilConjectures.scalarOrdinaryTensorChain_existsUnique`. Added zero holes and
zero split-off statements. The complete final module compiled through
`lcompile.py` in 44.5 seconds, exit code 0, with no warnings. All profiling commands
and diagnostic options were removed.

The nine unchanged holes remaining are:

- `WeilConjectures.scalarPullbackLevel_existsUnique`
- `WeilConjectures.scalarPullbackTower_existsUnique`
- `WeilConjectures.scalarTensorLevel_existsUnique`
- `WeilConjectures.scalarTensorTower_existsUnique`
- `WeilConjectures.scalarPullbackOrdinary_existsUnique`
- `WeilConjectures.scalarTensorOrdinary_existsUnique`
- `WeilConjectures.scalarCompletion_existsUnique`
- `WeilConjectures.scalarHomOrdinary_isIso`
- `WeilConjectures.scalarOperationsOrdinary_tower`

These belong to `lem-pur-integral-operations-scalar-extension`;
`scalarCompletion_existsUnique` also has the dedicated node
`lem-weil-normalized-scalar-completion`.

## No longer needed

None. No current Lean declaration, import, node or module was withdrawn. The
ordinary chain comparison uses the generic scalar tensor theorem without
completed-operation or tower-coherence lemmas for that step; those dependencies
remain needed by the other declarations and their proof plans.

## Where the brief, the DAG or earlier work was wrong

The shared source changed during this session when Q8's earlier tower
decomposition was taken out of the candidate (return dated 2026-10-26 04:51 UTC).
This packet keeps the current single `scalarOperationsOrdinary_tower` hole and
does not restore the three returned component declarations. The current source
has ten holes, while the assignment queue still records twelve. The parent node's
stale completed-decomposition step and its six absent component declaration names
were removed; the earlier mathematical tower plan and the historical clause nodes
are retained.

The ordinary chain tensor normalization already has an existence construction in
`ringedFiniteFreeHomBaseChange_complex`; no new balanced tensor construction or
split-off theorem is needed. Uniqueness follows from the scalar adjunction and
total tensor universal property.

The current blueprint moved `def-weil-derived-pullback-tensor-hom` to
`sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/` and now defines the
integral operations as condensed derived operations, referring coefficient
compatibility to `sk-prop-scalar-six`. The old source path and integral/common-stage
paragraph quoted in this module's node no longer occur there in
`literature/blueprint/latest`. This delivery preserves the assigned Lean contract
and proves its ordinary tensor generator statement, preserving the higher unit
route and target meanings.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
