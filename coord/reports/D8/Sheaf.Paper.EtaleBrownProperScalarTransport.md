## What changed

Split the long proper scalar transport proof into two strictly simpler public
subclaims and combined them in `etaleBrownProperScalarTransport`. The mate
invertibility subclaim and the normalized realization square remain explicit
named theorem holes with their source arguments recorded in their docstrings.

## Proved and sorry left

The target theorem `etaleBrownProperScalarTransport` is reduced to the two
subclaims and its combination proof compiles. The following newly named holes
remain:

- `etaleBrownProperScalarMate_isIso` (finite proper projection gives invertibility).
- `etaleBrownProperScalarSquare` (normalized cochain transport square).

## No longer needed

None. The target's declared dependencies remain represented by the two split
subclaims; no imported module was pruned.

## Where the brief, the DAG or earlier work was wrong

The original single proof step combines mate invertibility and the realization
square, which are independent substantial arguments. The DAG is updated to
record the two strictly simpler obligations and the target's proof now combines
them by constructing the inverse of the mate.

## New nodes

- `lem-pur-etale-brown-proper-scalar-mate-is-iso`
- `lem-pur-etale-brown-proper-scalar-square`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.EtaleBrownProperScalarMateIso": "c3bb3ff72e67d18957d60166574ab9b628117eab", "Sheaf.Paper.EtaleBrownProperScalarSquare": "5833b762b6b81b71b899d5156bbd4aa7f81a818a", "Sheaf.Paper.EtaleBrownProperScalarTransport": "fd06a42641162fb3ea80b9fdcf7bd470a4e0835e"}, "results": {"Sheaf.Paper.EtaleBrownLevelComparisons": {"hash": "e09d064564846ac276b9f0c7829c8466ee06fa2d", "status": "OK"}}, "seconds": 41, "time": "2026-10-28T03:33:24+0800", "transitive": 0, "version": 1}
```

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
