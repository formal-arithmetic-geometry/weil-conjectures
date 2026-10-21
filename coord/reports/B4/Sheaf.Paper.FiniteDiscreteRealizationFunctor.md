## What changed

Restored `lean/Sheaf/Paper/FiniteDiscreteRealizationFunctor.lean` from the exact
archive named by its `coord/rework.tsv` row,
`quarantine/Sheaf/Paper/FiniteDiscreteRealizationFunctor.lean`. The library path
was absent following the cluster restore; the archive was not withdrawn.
This restores the concrete derived realization, its shift/triangulated/full
instances, the single-complex essential-image proof, the three-square arrow
comparison, and the cached specified exchange-step interface. No archived
signature, definition, proof, import, or DAG attachment was changed.

Validation: the restored complete module compiled through `lcompile.py` in
10.7 seconds, with exit code 0 and no diagnostics. Read both attached nodes and
the fullness dependency's declaration. LeanFinder and Loogle confirm the
existing `Functor.mapDerivedCategorySingleFunctor` API used by the proof;
grep confirms `Arrow.isoMk`. The archive already implements the shortest
formal route: compose the two exact-functor single-complex comparisons and
the sheaf isomorphism; compose commuting squares using `Arrow.isoMk`.

The three cached exchange-step definitions are still the original specified
steps, as certified by their restored `_eq_original` theorems and the
factorization theorem. Their current upstream definitions were checked.
Restoring the archived public interface also preserves its quarantined
consumers (including `FiniteDiscreteCoefficientExchange`,
`FiniteDiscreteExchangeRealization`, `FiniteDiscreteCoefficientEncoding`,
`CoefficientDerivedFunctorAPI`, and `CoefficientExchangeFromComparisons`).
There is no definition or statement change, so no change record or consumer
adaptation is required. No adopted-source file was edited.

## Proved and sorry left

The archive contains zero `sorry`; the restored item also contains zero.
Holes closed: none (0 of 0). Holes added: none. Split off: none.
This delivery repairs the missing module rather than claiming new hole closure.

The restored complete proofs include
`FiniteDiscreteThreeStepComparison.nonemptyArrowIso`,
`FiniteDiscreteThreeStepComparison.nonemptyArrowIsoOfFactorizations`,
`FiniteDiscreteFactoredComparison.nonemptyArrowIso`,
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteRealization_single`,
and all seven exchange-step equation/factorization theorems.
The single-realization node is
`lem-weil-pbc-finite-discrete-single-realization`; the arrow comparison node is
`lem-weil-pbc-three-step-arrow-comparison`. The fullness instance retains the
existing `finiteDiscreteEtaleRealization_full` dependency; this report does not
claim to close any holes in that dependency's transitive proof closure.

## No longer needed

None. All archived imports, declarations, node attachments and dependencies
are retained. No nodes or modules are pruned or withdrawn. The unit route is
unchanged, and no new node is introduced.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantine restoration, not an unproved module.
Its rework row records removal after a cluster restore rather than a specific
mathematical or elaboration defect. The exact archived module now compiles
against the current server library. No current numbered return for this item
appears in `coord/returns/B4.md`.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
