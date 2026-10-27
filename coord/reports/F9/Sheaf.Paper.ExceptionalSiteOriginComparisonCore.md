## What changed

Proved `AlgebraicGeometry.exceptionalSiteOriginComparison_evaluation_bound` by applying
exactness of the concrete coefficient evaluation and transporting the lower bound across
the package's derived factorization. Proved
`AlgebraicGeometry.exceptionalSiteOriginComparison_level_inverse_bound` similarly from the
finite inverse-image exactness recorded in `C.ordinary` and its derived factorization.
Added a private factorization-isomorphism helper and retained the existing public interface.
The core construction theorem remains unchanged.

## Proved and sorry left

Closed two declarations:

- `exceptionalSiteOriginComparison_evaluation_bound`.
- `exceptionalSiteOriginComparison_level_inverse_bound`.

One sorry remains in `exceptionalSiteOriginComparison_core` (node
`lem-sf-exceptional-site-origin-comparison-core`). No new sorry declarations were added.

## No longer needed

The proof does not use the previously listed system-level evaluation-bounds dependency for
the two bound lemmas; it uses the concrete exact evaluation theorem and derived
factorization API directly. The corresponding proof dependency edges were removed from
nodes `lem-sf-exceptional-site-origin-comparison-bound` and
`lem-sf-exceptional-site-origin-comparison-level-bound`. No unit-level route was bypassed.

## Where the brief, the DAG or earlier work was wrong

The finite and system bound statements are directly consequences of exact functors and
factorization isomorphisms, so the generic system-evaluation theorem and generic derived
adjunction-bound theorem are unnecessary. The core construction still requires the
substantial ordinary/derived comparison construction described by its node; its existing
hypotheses do not expose the regularity and adic-completeness assumptions needed by the
available coefficient-system comparison existence theorem, so that hole is left in place.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalSiteOriginComparisonCore": "a838df68d6358fa96abbde7eabf35eda8fe0f092"}, "results": {"Sheaf.Paper.ExceptionalSiteOriginComparison": {"hash": "f3ed4c96d9bf6e76f735400732ddacf888e82c10", "status": "OK"}}, "seconds": 40, "time": "2026-10-28T03:40:30+0800", "transitive": 0, "version": 1}
```

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
