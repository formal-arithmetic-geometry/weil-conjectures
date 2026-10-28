## What changed

Replaced the original single global-invertibility hole by the affine-cover argument.
The proof obtains an affine closed chart, uses the existing closed coefficient descent
and finite smooth dualizing scalar theorems for its two component isomorphisms, cancels
the object identifications, and applies the jointly-surjective upper-star criterion.
The original theorem signature and its public import are unchanged.

Added `Sheaf.CategoryTheory.CounitMateTransport` for the proved general adjunction
transport calculation, compiled using only Mathlib imports. Added
`Sheaf.SixFunctors.ClosedOpenDualizingMate` for the real counit-defined closed mate,
and `Sheaf.SixFunctors.ClosedOpenDualizingMateNormalization` for the remaining
normalization statement.
the restricted global mate with the closed mate followed by the affine structural mate.
Added `Sheaf.SixFunctors.OpenClosedCompactScalar`: the remaining coefficient square
between the two presentations of the compact-support left adjoint. This statement
contains no exceptional coefficient map and no invertibility conclusion for dualizing
maps. The square applies to an arbitrary bounded constructible finite-Tor object.

Updated the item's DAG proof and attached nodes for the three new public transport and normalization
statements. No existing module besides the assigned item is changed.

## Proved and sorry left

The original hole in
`WeilConjectures.finiteDualizing_etaleComparison_isIso_for_factorization` is closed by
complete Lean glue from the named dependencies. In particular, the private closed-mate
and affine-space invertibility steps are proved, including the quotient annihilator and
the prime-to-characteristic unit calculation.

The new theorem
`AlgebraicGeometry.Etale.closedOpen_dualizingMate_normalization`
(node `dualizing-open-closed-mate-normalization`) is split off with its complete
source proof in words; its statement combines the left coefficient square, the
existing open-mate and closed-assembly calculations, and the proved adjunction
transport helper.

Three new holes remain: `WeilConjectures.closed_mate_isIso_aux`
(node `affine-closed-mate-isIso`) is the strictly smaller closed-chart invertibility step.
Two other new holes remain: `AlgebraicGeometry.Etale.closedOpen_dualizingMate_normalization`
(node `dualizing-open-closed-mate-normalization`) and
`AlgebraicGeometry.Etale.openClosedCompactScalar_coherence`
(node `open-closed-compact-scalar-coherence`). It is the left-adjoint coefficient
normalization square, with its source and full proof in words in its docstring.
There are no holes in definitions or private lemmas.

Direct counts in the changed files: one original hole closed, two lower holes added;
this is a decomposition with one extra categorical helper proved. This is a decomposition, not an independent proof of the
original hole. Previously existing
holes in imported chart and closed-descent theorems are used as intended by stage 3.

## No longer needed

No previously declared dependency or module is withdrawn. The direct public import
of `Sheaf.SixFunctors.ClosedOpenDualizingMate` is retained because the assigned
theorem uses its closed mate. Temporary proof imports of
`Sheaf.Paper.ExceptionalCoefficientComparison` in the item and
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality` in the left-square module
were removed because the final proof does not use them there. The original node listed
no proof dependencies, although its prose required closed-chart descent and affine
comparison; those dependencies are now explicit.

The already existing `FiniteDualizing` global theorem, `FiniteDualizingAffineRestriction`,
and `AffineRestrictionMapIso` cannot serve as shortcuts: their import chain returns to
this very item. The proof uses the smooth affine-space scalar theorem directly, so it
does not add an import of the separate `AffineDualizingCoefficient` presentation.
No source-library declaration is removed, changed, or replaced with a hole.

## Where the brief, the DAG or earlier work was wrong

The previous split supplied the same global `IsIso` obligation without recording any
of its geometric dependencies. Reusing the apparent proved global theorem would be
circular. This delivery separates the two actual geometric invertibility inputs from
the missing compatibility of the open and closed presentations of the left adjoint.
The remaining statement is strictly a coherence substep and makes no assertion that
the original dualizing coefficient map is invertible. The inherited `created.item`
chain uses module names, so `blueprint_refs.py ancestor` reports no ancestor; the
new nodes cite the actual blueprint lemma `lem-coef-finite-dualizing` directly,
with its precise paragraph and the intervening item nodes recorded.

Checked the new statements at an identity quotient, zero input, relative dimension
zero, and an empty open: the constructions use identity/zero normalizations and add
no nonemptiness or flatness hypotheses. No target or existing statement was weakened.

## New nodes

`open-closed-compact-scalar-coherence` records the remaining left-adjoint coefficient
square for two factorizations, in `Sheaf.SixFunctors.OpenClosedCompactScalar`.

`dualizing-open-closed-mate-normalization` records its proved adjunction transpose and
the real closed mate in `Sheaf.SixFunctors.ClosedOpenDualizingMate`. The isomorphisms in
its conclusion are constructed inside the theorem proof by right-adjoint uniqueness;
no definition chooses arbitrary data from an unproved existence theorem.

`counit-mate-transport` records the proved general categorical transport theorem in
`Sheaf.CategoryTheory.CounitMateTransport`. Its isolated Mathlib context avoids
elaborating generic adjunction calculations under the geometric instance environment.

The full sandbox import-order compile passed on 2026-10-28; the assigned module
compiled in 11.8 seconds.

`affine-closed-mate-isIso` records the remaining affine closed-chart descent step.
`closed-open-dualizing-mate` records the proved closed mate and scalar-map normalization helpers.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 5 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.CounitMateTransport": "b321461814abf55783bec84e69c01948c9848e3e", "Sheaf.SixFunctors.AffineRestrictionMapIsoAux": "7a47d7135a26cb90461a257e3038badf61288339", "Sheaf.SixFunctors.ClosedOpenDualizingMate": "5d4e465f5c9d2de0af3f530e24f31304bf81d7dc", "Sheaf.SixFunctors.ClosedOpenDualizingMateNormalization": "bbb242404d5883235a893a20eef562fd27729ad5", "Sheaf.SixFunctors.OpenClosedCompactScalar": "e8bc192cbf273422d11ae01db533c421e126c631"}, "results": {"Sheaf.SixFunctors.AffineRestrictionMapIso": {"hash": "d8710ad90d1915392bd5a36ad0a91a5f34bfa6e0", "status": "OK"}, "Sheaf.SixFunctors.CoefDualFormulaScalarTranspose": {"hash": "0f7df824dd97c32746df97be275b1933e9025c38", "status": "OK"}, "Sheaf.SixFunctors.CoefFiniteRealizationRestrictionSquare": {"hash": "a85cf96bef314c0c9e6e0aca11a0841220e72590", "status": "OK"}, "Sheaf.SixFunctors.DualizingSupportEvaluation": {"hash": "c495b06bb7f8ca6bfe591f0e39e3073225f3b720", "status": "OK"}, "Sheaf.SixFunctors.IntegralDualizingFiniteBounds": {"hash": "b2a8e3df239cf54ffce078a0ccd32bbfd4068ec8", "status": "OK"}}, "seconds": 75, "time": "2026-10-28T12:48:23+0800", "transitive": 4, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
