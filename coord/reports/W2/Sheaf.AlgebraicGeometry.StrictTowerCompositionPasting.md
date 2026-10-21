## What changed

Prove `compositionPastingCoherence` and `compositionCommonCoherence` by the node's
finite-origin, six-square refinement and base-change cube calculations. Establish
invertibility using finite-origin preservation by open extension. Prove refinement
and base-change equations first with abstract functors and then identify all factors
with the library transformations. Use the existing proved strict-tower direct-image
coherence for proper associativity and mate pasting. Derive the right unit from the
inverse-image right-unit law. Common-refinement independence uses the hf clause of
refinement/exchange coherence and cancellation of the invertible composition map.

The private calculation uses the existing pinned comparisons from
`RefinementExchangeCoherence`, whose proved equality specifications identify exactly
the original comparisons. No arbitrary existence witness supplies any data.

Normalize four definition bodies in the unclaimed `StrictTowerCompositionMaps`:
`compositionD`, `compositionC`, `compositionE`, `compositionHorizontalE`. Remove only
identity associator/unitor factors and preserve all signatures and nonidentity
comparisons. Adapt the two affected factorization proofs of the latest, fully proved
`RefinementExchangeCoherence` module. The change record is
`coord/changes/W2-strict-tower-composition-normalization.md`.

All three delivered modules compile together, in import order: maps 6.6 s,
refinement/exchange 9.6 s, item 15.3 s. No compile limit was raised.

## Proved and sorry left

Closed both original holes (2 of 2):

- `AlgebraicGeometry.ProEtale.StrictTower.compositionPastingCoherence`.
- `AlgebraicGeometry.ProEtale.StrictTower.compositionCommonCoherence`.

Added zero holes; split off zero statements. Every delivered module has zero
remaining `sorry`. Existing stated dependencies, including the normalized calculus,
are used as specified by stage 3. The completed H4 proof is preserved, not replaced
by its earlier holed version.

## No longer needed

No node or module is withdrawn. Every declared proof dependency remains used,
directly or through the existing normalized operations and coherence. Add the
already proved `lem-cbc-strict-tower-direct-image-coherence` dependency for named
proper associativity and mate pasting. Public imports are preserved; proof imports
are private.

The generic `ProperOpenTowerRefinement` theorem is unnecessary: it requires
invertibility of gamma on every input, whereas this item's invertibility is limited
to finite-origin inputs. The abstract pasting calculation here assumes no such
invertibility and proves the actual unrestricted transformation equations.

## Where the brief, the DAG or earlier work was wrong

The mathematical statements and ten-step plan are valid. Their canonical composition
identifications require the named proper associativity and right-unit equations,
which the implementation supplies explicitly. Direct specialization of component
calculations unfolded large derived constructions and exceeded the compile limit.
An abstract record of functors and calculus laws, pinned comparison equalities,
whole-transformation transport, and removal of identity factors avoid that unfolding.
The new direct-image coherence dependency became available during this session and
supplies the existing proof of the needed associativity and mate-pasting laws.

## Forced adaptations

`Sheaf.Paper.RefinementExchangeCoherence` is currently unclaimed; H4 completed it
during this session. Its unchanged current source, compiled against the normalized
maps, fails at original lines 162 and 588 with `Tactic rfl failed`: respectively
`compositionC` is not definitionally the old `refinementPasting` and `compositionE`
is not definitionally the old `exchangePasting`.

Add the proved private helpers `refinementPasting_normalized` and
`exchangePasting_normalized`. Replace only the final factorization steps of
`refinementComparison_factor` and `compositionE_factor` by the corresponding symmetric
helper equalities. Bind the two quasi-compactness proofs already present in the
first theorem's let-bound statement. All existing signatures, visibility, imports,
definition bodies and other proofs remain identical. The unchanged original fails
at precisely those two proofs; the adapted module compiles in the delivered packet.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
