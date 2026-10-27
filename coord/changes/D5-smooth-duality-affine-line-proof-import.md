# sfAffineLineCanonicalDuality proof import

## Reason

The unused private import EtaleFiniteTwistPullback reaches SmoothDuality through
EtaleFiniteTwistPullbackBase and the upstream smooth-purity modules. It therefore
prevents SmoothDuality from using the already stated affine-line input. Remove
that private import. The affine-line theorem remains unchanged with its existing
named sorry; its future proof must use an acyclic lower-level twist API.

## Old

```lean
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
```

## New

The private import is absent. All public imports, declarations, signatures,
definitions and the theorem body remain byte-for-byte unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfAffineLineCanonicalDuality | unclaimed | Remove one unused private import; compiled successfully. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | D5 | New private proof imports and proved private helpers fill its one hole. |

The source-only downstream query found zero current downstream modules of the
affine-line input and only its defining occurrence of sfAffineLineCanonicalDuality.
The item adds a proof-only consumer; no public API changes. Its local braiding
priority agrees with upstream SmoothDuality.Local and affects only elaboration
inside the file. No existing public imports or declaration attributes change.

## Status

landed 20261023T151814-L-411065 2026-10-23 (merge of deliver/D5/WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality)
