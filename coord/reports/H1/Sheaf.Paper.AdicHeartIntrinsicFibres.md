## What changed

Retained the earlier attempt and checked it against the current source. Proved
`WeilConjectures.sfAdicRationalFiber_existsUnique` by localization of the actual
additive completed fibre. The proof shows that a uniformizer power divides an
integer power of the coefficient prime, whose image is invertible over E, and
uses exactness of distinguished triangles to invert the rationalization class.
Proved `WeilConjectures.sfAdicHeartPullbackFibres` by combining the twelve
published raw assertions with the intrinsic common-stage existence theorem.
All existing signatures and definitions are preserved.

## Proved and sorry left

Closed two of the original three holes:
- `WeilConjectures.sfAdicRationalFiber_existsUnique`.
- `WeilConjectures.sfAdicHeartPullbackFibres`.

One existing hole remains:
- `WeilConjectures.sfAdicCommonFiber_exists`
  (`lem-per-adic-heart-pullback-fibres`).

No holes added and no statements split off. The retained rational descent proof
and conjunction proof compiled twice on the remote compiler (8.0 and 8.4 seconds).
Those checks emitted only the unused IsAlgClosed section-variable warning. A scoped
linter setting now preserves that existing theorem signature while silencing the
warning; compilation of that final setting has not been verified because the
compile service stopped responding. The common-stage theorem remains unfinished.

## No longer needed

No imports or nodes pruned. An experiment removing unused proof imports could
not be validated because the compile service timed out; it was reverted. All
original imports are retained, with one new private proof import:
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom`.

## Where the brief, the DAG or earlier work was wrong

The previous session was blocked by remote compiler availability. The compiler
responded successfully twice in this session, then repeated lcompile.py requests
and the required deliver3.py --no-push dry run failed before any Lean output,
reporting that the compile server was busy or unreachable. The dry run reported
COMPILE FAILED (local), nothing pushed. This is a transport/service failure, not
a Lean file exceeding its 60-second execution allowance. All work is retained
in the sandbox; no delivery was pushed.
No source statement has been changed. The common-stage existence statement has
arbitrary W, whereas the raw common-fibre assertion is for finite-type Base k;
using that assertion alone would require hypotheses absent from this theorem.

Both required dry-run attempts failed in the compile transport (212 s, then
206 s without server output). The last direct compile retry also failed with
exit 124 after 207 s without server output. No Lean timeout diagnostic was
received. Resume with the required dry run; report.md and the item are present.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
