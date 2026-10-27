## What changed

Proved `WeilConjectures.IntegralSystemRealization.integralRefinementDiagramAdmissibility`
with its original signature and every existing definition unchanged. Only the item Lean
module and its theorem node are changed. Added proved private helpers for Tor transport
and widening, dimension bounds, cohomology from a flat model, sharp local estimates,
and the structural interval induction.

The existing `completedShriekIntegralBounds` supplies the full intermediate domain and
integral constructibility for every geometric support word. The proof checks all eighteen
words, then proves the sharper prescribed intervals independently from the finite-level
open and direct-image theorems. It takes finite upper bounds and derives the final
whole-system equation from `Realizations.normalization` by actual functorial cancellation.

The uniform field-extension dimension bound is specialized to the identity pullback;
no absolute separatedness or nonemptiness is used. Empty sources admit natural bound
zero, and the proof and interval widening cover identity refinements and zero inputs.
The helper for cohomological support uses the bounded-flat-model equivalence and the
homology factorization, so it does not assume cohomological bounds from Tor by definition.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralSystemRealization.integralRefinementDiagramAdmissibility`
(node `lem-sf-integral-refinement-diagram-admissibility`). Added zero holes and zero
split-off statements. No `sorry` remains in the delivered module. This proof uses
existing library theorems; no claim is made here that all their dependencies are closed.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound`
- `Sheaf.Paper.ProEtaleScalarMateNormalization`
- `Sheaf.Paper.ProperEtaleOriginScalarIsomorphism`
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.Paper.NormalizedEtaleOriginWitnesses`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.CoefficientSystemDerivedComparison`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`

The theorem no longer directly invokes the original planned nodes
`lem-cbc-compactification-geometry-fibre-bound`,
`lem-fix-proetale-scalar-mate-normalization`,
`lem-fix-proper-etale-origin-scalar-isomorphism`,
`lem-pur-coefficient-system-derived-comparison`,
`lem-pur-normalized-actual-reconstruction-maps`,
`lem-sf-open-tensor-normalization`,
`lem-weil-pbc-finite-ring-constructible-derived-origin`, or
`lem-weil-pbc-normalized-etale-origin-witnesses`. The source field-base dimension
lemma replaces the geometry-cover route. The existing support-word theorem packages
the normalization and origin work, so it is reused instead of duplicating those proofs.
These nodes and their modules may still be needed transitively or by other parents;
none is withdrawn or claimed globally pruned.

The old direct proof-dependency entries for
`def-weil-derived-complete-integral-detailed`, `def-weil-finite-tor-amplitude`,
`def-weil-proper-morphism`, and `lem-sf-integral-compactification-system-realization`
are unnecessary as proof steps: their interfaces remain available through unchanged
statement dependencies and public imports. No public import or definition is changed.
The DAG proof and dependency union now record the actual argument; obsolete direct
`tool_uses` entries are removed, with no approvals added or reordered.

## Where the brief, the DAG or earlier work was wrong

The current server queue row assigns one proof hole, rather than a zero-hole repair.
The older rework/build-error records name failed imports; the baseline module now
compiles against published dependencies. Its old proof plan is mathematically usable,
but duplicates the support-word domain induction already proved in
`completedShriekIntegralBounds` in the same compatibility unit. The new proof reuses
that result and retains the independent sharper interval induction required here.

`lem-sf-flat-model` and `lem-weil-structure-direct-images-constructible` are used only
as generic tools: the bounded-flat-model equivalence and coefficient-prime
invertibility. The source field-extension dimension lemma is also a generic geometry
tool. No unit-level statement, proof route, target, or definition is altered. There
are no new nodes and no forced adaptations.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility": "c9ca590006ea33446458683baec90833ab6151b1"}, "results": {"Sheaf.SixFunctors.IntegralNormalizedRefinementPasting": {"hash": "31b61092d773c1704bf225bb20f80dc24ee3cf9f", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T00:42:58+0800", "transitive": 0, "version": 1}
```

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
