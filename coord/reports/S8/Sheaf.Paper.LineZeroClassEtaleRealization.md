## What changed

Proved `WeilConjectures.PurityFiniteSetting.line_zero_geometry` in
`Sheaf.Paper.LineZeroClassEtaleRealization` from
`PurityVectorBundle.lineZeroGeometry` and closed pro-etale direct-image exactness.
The proof constructs the compactifiability instances from projective completion and
the section identity, and checks the Cartier assertion after arbitrary base change.
All existing declaration signatures and definition bodies are unchanged.

The added imports are private proof imports of `Sheaf.Paper.LineZeroGeometry` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`.
The node records the completed geometric step and retains the original plan for
the still-open realization theorem. No new nodes or definition repairs are delivered.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.PurityFiniteSetting.line_zero_geometry`.

One original hole remains:
`WeilConjectures.PurityFiniteSetting.line_zero_class_etale_realization`
(node `lem-pur-line-zero-class-etale-realization`). Its body remains `by sorry`.
There are zero holes added and zero split-off statements. This is a partial delivery.

## No longer needed

Removed these redundant private imports from the item:

- `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.Paper.ClosedFiniteAdjointCounitTransport`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `Sheaf.Paper.CompactSupportSiteCoherence`

No node or module is withdrawn. The Cartier-relative-realization and closed-section
compact-origin dependencies remain needed by the unfinished theorem's proof plan.
No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original geometric step did not explicitly record the closed direct-image
exactness lemma needed by its last conjunct; the node now records it.

The generic closed-section theorem uses literal pro-etale constant sheaves, whereas
the item uses comparison-image constants. Applying that theorem requires the
canonical coefficient transport, including naturality of the proper and derived
single-object comparisons. Direct specialization does not prove the final two
conjuncts. Experiments exposed costly definitional conversions through the
`functorialCupHasDerived` and abelian-instance aliases. Those experiments and
alternative coefficient presentations are not part of this delivery; no held
module, public definition or target statement has been changed.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
