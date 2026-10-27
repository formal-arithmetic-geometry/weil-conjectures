## What changed

Filled two existing theorem proofs in `Sheaf.Paper.DerivedAutomorphismHomEvaluation`.
`podHomComplexShift_existsUnique` composes the proved independent-universe target and
source Hom-complex shifts with the shift-addition comparison. Its projection formula
has exactly the specified sign; a transport lemma handles equal integer degrees, and
joint monicity of the Hom-product projections gives uniqueness.
`podCompletedToTower_laws` composes the actual three naturality squares and applies
unrestricted normalized reconstruction to its actual adjunction unit on constructible
complete inputs. An auxiliary finite field datum translates the existing completeness
property through `sfDerivedComplete_iff_legacy`.

The existing proof import of `RingedInternalHomShiftOfUniverses` now uses `import all`
to access its proved ordinary shift helpers. Added private proof imports of
`PurNormalizedReconstructionAdjunctionCalculus` and `SfDerivedCompleteLegacyComparison`.
No declaration signatures, definitions, public imports, or target statements changed.
Local irreducibility annotations keep the chosen Hom bifunctor and coefficient
calculus from unfolding during elaboration. The existing main DAG node records
these two proof routes and their dependencies.

## Proved and sorry left

Closed 2 of the original 28 holes, with no added holes and no split-off statements:

- `WeilConjectures.podHomComplexShift_existsUnique`.
- `WeilConjectures.podCompletedToTower_laws`.

The following 26 existing theorem holes remain unchanged. Every one belongs to
`lem-pod-derived-automorphism-hom-evaluation`, whose source and natural-language
proofs are in their original docstrings and DAG record:

- `WeilConjectures.podFiniteHomComparison_laws`.
- `WeilConjectures.podIntegralHomComparison_laws`.
- `WeilConjectures.podRationalClosed_existsUnique`.
- `WeilConjectures.podRationalHomComparison_laws`.
- `WeilConjectures.podCommonClosed_existsUnique`.
- `WeilConjectures.podCommonHomComparison_laws`.
- `WeilConjectures.podSystemHomComparison_laws`.
- `WeilConjectures.podFiniteRestrictionOrdinary_existsUnique`.
- `WeilConjectures.podOrdinaryLimitReindexing_existsUnique`.
- `WeilConjectures.podLimitReindexing_existsUnique`.
- `WeilConjectures.podReductionReindexingMap_laws`.
- `WeilConjectures.podHomReductionSquare`.
- `WeilConjectures.podDerivedHomShift_existsUnique`.
- `WeilConjectures.podFiniteHomComparison_shift`.
- `WeilConjectures.podFiniteHomComparison_comp`.
- `WeilConjectures.podIntegralReindexedHom_shift`.
- `WeilConjectures.podCompletedModuleComp_existsUnique`.
- `WeilConjectures.podIntegralPullbackComp_normalization`.
- `WeilConjectures.podIntegralHomComparison_comp`.
- `WeilConjectures.podSystemNormalized`.
- `WeilConjectures.podSystemHomComparison_fiber`.
- `WeilConjectures.podArgumentFirst_integral_rational`.
- `WeilConjectures.podArgumentFirst_common`.
- `WeilConjectures.podRationalHomComparison_comp`.
- `WeilConjectures.podCommonHomComparison_comp`.
- `WeilConjectures.podIntegralRationalHomComparison_shift`.

## No longer needed

None. No existing imports, nodes, or modules are withdrawn. The remaining companions
still need the retained dependency plan. For the ordinary signed double shift itself,
the proof uses the already proved `RingedHomUniverses.ordinaryRightShift` and
`ordinaryLeftShift` rather than reconstructing resolutions or using scheme-specific
reindexing-coherence data. For the complete-input invertibility clause it directly uses
unrestricted normalized reconstruction instead of a new finite-free E/E comparison.
These local shortcuts do not make any whole existing dependency module unnecessary.

## Where the brief, the DAG or earlier work was wrong

The main node lists `lem-pod-reindexing-system-hom-reduction-square` as a proof dependency,
but its attached module `Sheaf.Paper.ReindexingSystemHomReductionSquare` publicly imports
this item. It cannot be directly imported here without a cycle. The associated holes
are untouched; resolving that interface is outside these two completed proofs.

The node's historical blueprint path has moved. The current text was checked at
`literature/blueprint/latest/blueprint/sec-poincare-duality/sk-thm-frobenius/` in
`prop-pod-dual-tate-data-compatibility.proof.md`. Its route is retained.

The unrestricted reconstruction declaration initially postdated the published green
build. The next compile uses the published build containing that declaration.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
