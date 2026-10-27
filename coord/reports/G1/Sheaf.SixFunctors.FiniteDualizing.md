## What changed

Replaced the single hole in `WeilConjectures.finiteDualizingCoefficientComparisons` by a proof assembling compact-support invertibility, the literal exceptional counit equation, affine-local descent, the generic coefficient counit-mate unit/cocycle, and intrinsic scalar transport. The statement is unchanged (checked against the original signature verbatim). All five delivered Lean modules have compiled through `lcompile.py`; the final item compile passed in 32.2 seconds.

Extracted the preceding data and already proved lemmas verbatim into `Sheaf.SixFunctors.FiniteDualizingData`, publicly reexported by the item, to let the three subarguments refer to the specified objects without importing the theorem they prove. This was done before encountering compile-time limits, not to evade a limit. The nine original public imports remain visible through this reexport. All additional theorem imports are private proof imports. Profiling isolated a 27.6-second inference in `finiteDualizingIntrinsicRes_additive`; its proof now verifies addition directly on sections, with the same instance type and data.

## Proved and sorry left

Closed the original hole `WeilConjectures.finiteDualizingCoefficientComparisons` (node `lem-coef-finite-dualizing`). The compact comparison and counit identity are proved directly. Private helpers prove global etale invertibility from affine restrictions and prove the etale unit and cocycle from pre-transposition normalization using the existing proved generic mate lemmas.

Added three holes, one per new module:

- `WeilConjectures.finiteDualizing_affineRestriction_isIso` (`lem-coef-dualizing-affine-restriction`): only the affine restriction of the etale comparison is invertible.
- `WeilConjectures.finiteDualizing_compact_normalization` (`lem-coef-dualizing-compact-normalization`): compact support and regular scalar units respect quotient identity/composition, without any exceptional comparison.
- `WeilConjectures.finiteDualizing_scalar_realization` (`lem-coef-dualizing-scalar-realization`): arbitrary-family scalar-adjunction transport through the normalized realization.

The item has zero remaining holes, the data module has zero, and the delivery has three. This is a decomposition of one original hole into three genuine subarguments, not a claim of net sorry reduction. Every remaining hole is a public named theorem, with its complete proof in words and a matching node. No data is selected from a new unproved existence statement.

## No longer needed

No modules are withdrawn and no source-library declarations are removed. The affine-space, closed-chart, closed-site, closed-descent, closed-assembly and open-locality dependencies remain needed by the affine subargument. The former parent dependencies are redistributed to the relevant new nodes; none is claimed globally pruned. No original public import is lost. Removed the redundant explicit `Sheaf.Paper.EtaleCompactScalarCoherence` import from the new normalization module; it is already publicly available through the data module. The generic site-mate transport lemmas do not alone identify the concrete intrinsic restriction square, so the remaining scalar-realization node records that exact missing compatibility rather than pretending it follows solely from categorical conjugation.

## Where the brief, the DAG or earlier work was wrong

The plan gives the geometric and mate ingredients, but the supplied declarations do not directly provide the identity/composition normalization of the concrete compact-support maps or the coherent intrinsic realization restriction square. Those are isolated explicitly rather than moving the whole theorem under a new name. The compact-support comparison is invertible on every object here by the existing proper finite-coefficient theorem and the open factor, so this clause needs no extra constructibility lemma.

## New nodes

`def-coef-finite-dualizing-data` records ownership of the existing verbatim definitions and proved helper lemmas in the new data module. No new mathematical data or choice is introduced. Change record: `coord/changes/finite-dualizing-data-extraction.md`; it lists all 137 downstream consumers and confirms their meaning is unchanged.

`lem-coef-dualizing-affine-restriction` is the affine-local invertibility step, retaining the unit route through closed affine-space charts and counit-compatible open restriction. Edge cases: the empty affine open, equal coefficient levels, and nonflat quotient maps are included.

`lem-coef-dualizing-compact-normalization` isolates the proper/open coefficient identity and composition equations before taking exceptional mates. It applies to arbitrary objects and involves no dualizing invertibility assertion. Equal levels and a nonflat quotient use the same sectionwise balancing equations.

`lem-coef-dualizing-scalar-realization` isolates the normalization and scalar adjunction transport step for arbitrary families on any scheme. It assumes the ordinary invertibility and coherence already proved in the item; it constructs neither compact support nor exceptional inverse images and asserts no ambient pro-etale exceptional adjunction. Arbitrary endpoint isomorphisms are harmless because they cancel by naturality, including at the identity level.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
