## What changed

Filled `WeilConjectures.NormalizedRingCompactScalar.normalizedRingCompactScalarCocycle`
without changing its statement or any existing definition, structure field, or public import.
The ambient clauses use the existing `PurCompactSupport.comparison_composition` and
`PurCompactSupport.comparison_identity`. Their general signatures cover arbitrary actual
coefficient maps, including nonflat quotients and completed/finite composites.
The restricted composition and identity clauses are proved by naturality, the supplied
normalization equations, cancellation of realization isomorphisms, and faithfulness of
the ring-stage inclusions. Uniqueness is proved directly by the same cancellation.
Proved private helpers supply faithfulness of the ring-stage inclusions and perform
the unit calculation in abstract categories. A private explicit identity change and
its extensionality lemma reduce arbitrary identity presentations to reflexive transports,
avoiding expansion of the derived scalar-extension implementation. The node records this proof route. No other existing module is edited.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.NormalizedRingCompactScalar.normalizedRingCompactScalarCocycle`.
Added zero holes and split off zero statements. No sorry remains in the delivered module.
The ambient laws cited from `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`
are already named statements with their own source, proof plan, and DAG attachment;
their existing holes are not added by this delivery.

Validation: the completed module compiled cleanly through `lcompile.py` in 15.9 seconds,
with no warnings, profiling settings, raised limits, or remaining `sorry`. The delivery
command runs the remaining signature, node, import, and axiom checks.

## No longer needed

Removed the private proof imports `Sheaf.Paper.RingedCoefficientPullbackCoherence`,
`Sheaf.Paper.RingedCoefficientProjectionCocycle`, and
`Sheaf.SixFunctors.OpenTensorNormalization`. Their corresponding nodes
`lem-pur-coefficient-pullback-coherence`, `lem-pur-ringed-coefficient-projection-cocycle`,
and `lem-sf-open-tensor-normalization` are no longer direct proof dependencies of this
item; their obsolete tool-use entries are removed. The item also no longer needs
`def-pur-integral-compact-support-coefficient-data` as a direct proof dependency
(its definitions remain statement prerequisites through the existing public imports).
The exact ambient comparison laws already package the proper/open calculation.
No module or declaration is withdrawn; these dependencies may remain needed elsewhere.
The unit route and all public prerequisites are retained.

## Where the brief, the DAG or earlier work was wrong

The planned Steps 1–3 repeated an ambient cocycle and identity that are already stated
in the coefficient comparison library, with precisely the required generality.
Reusing those statements shortens the proof without introducing any hypothesis.
The restricted calculation uses no inverse of an ambient proper comparison.
Edge cases are covered by the same formal proof: identity or empty geometry,
identity coefficient maps, nonflat finite quotients, mixed ring stages, and arbitrary
presentations of composite maps. No statement correction or definition repair is needed.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
