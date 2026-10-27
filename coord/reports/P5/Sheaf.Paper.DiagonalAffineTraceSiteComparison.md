## What changed

Repaired returned delivery a82f51e13c6 against the current source. The return reported
that reviewer C-a82f5 passed the mathematics but landing failed because --apply-fixes
used the change-record basename instead of its delivery path. The refreshed record
is included at coord/changes/P5-diagonal-affine-trace-site-data.md and now contains
the current source verbatim, including Z7's already-proved auxiliary theorems.
No reviewer-applied correction is needed for the stale proof or hole-count claims.

The main theorem unfolds Conclusion, quantifies over every presentation and
annihilator, combines three strictly smaller geometric statements, and obtains the
projective-line normalization from projectiveComparison. The three statements are
actual-map agreement (two arrows), the independent integration square, and rank-zero
identity normalization. Each has its own module, source, proof plan and DAG node.

Extracted the existing data to DiagonalAffineTraceSiteData to avoid an import cycle.
All existing public names, signatures, attributes, definition bodies, auxiliary proofs
and public prerequisites are preserved verbatim through reexport. The extraction
separates mathematical dependencies; it is not a compile-time workaround.
The parent node is refreshed from the current source with only the delivered proof,
proof dependencies, proof origin and Lean attachment overlaid.

## Proved and sorry left

The current source has one hole:
WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.diagonalAffineTraceSiteComparison.
Its assembly proof is complete, including projective normalization, conditional on
three split statements. This is a decomposition, not a completed geometric proof.

Three new whole-theorem sorry statements remain:

- WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.diagonalAffineTraceMapAgreement
  (lem-pur-diagonal-affine-map-agreement).
- WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.diagonalAffineIntegrationSiteSquare
  (lem-pur-diagonal-affine-integration-site-square).
- WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.diagonalAffineRankZeroActual
  (lem-pur-diagonal-affine-rank-zero-actual).

One current textual hole is closed and three are added: net two additional holes.
No sorry remains in the item or the shared data. The following pre-existing proofs
are preserved, not counted as newly proved by this rebased delivery:
integrationInput_existsUnique, ordinaryPlus, rankZeroOrdinarySource_existsUnique,
and the private baseCoefficient_bounded helper, all in the same namespace.
No definition contains sorry or uses a new existence-only witness.

All five rebased modules compiled successfully on the launcher server.
The delivery command additionally runs its compile and preflight checks.

## No longer needed

No mathematical dependency, node or module is withdrawn. The geometric prerequisites
remain in the corresponding three proof plans. The original four public imports
move verbatim to the shared data module and remain publicly reexported; none is
pruned. The auxiliary proof imports also move there, unchanged from current source.
The assembly imports only the three split statements and the shared data.

## Where the brief, the DAG or earlier work was wrong

The returned report incorrectly treated all four original holes as current and
claimed three new auxiliary proofs. The current source already contains Z7's three
auxiliary proofs. This repair preserves them verbatim and corrects the count to one
hole decomposed into three. The old/new change-record blocks now match this source.
The landing error identifies a basename passed to --apply-fixes; the actual record
in this packet uses the full path coord/changes/P5-diagonal-affine-trace-site-data.md.

The geometric dependencies use different source presentations. The named steps
isolate the remaining coordinate and mate comparisons; the parent statement and
unit route are unchanged. Edge cases checked in the original reviewed reduction:
rank zero, zero input, empty scheme, either ordering of annihilating and diagonal
exponents, and ramified positive coefficient levels. No divisibility or coefficient
flatness hypothesis is added.

## New nodes

`def-pur-diagonal-affine-trace-site-data` owns the existing data block, including
MapAgreement, TraceSquare, RankZeroActual and Conclusion, with its already-proved
auxiliary theorems. Change record: coord/changes/P5-diagonal-affine-trace-site-data.md.

`lem-pur-diagonal-affine-map-agreement` is original proof steps 1--3 restricted to
the two actual intrinsic maps and their specified transported coordinates.

`lem-pur-diagonal-affine-integration-site-square` is original proof step 3 restricted
to the actual compact-support integration square at every rank and annihilator.

`lem-pur-diagonal-affine-rank-zero-actual` is original proof step 4 restricted to
identity-adjunction normalization in the independent unit coordinates.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
