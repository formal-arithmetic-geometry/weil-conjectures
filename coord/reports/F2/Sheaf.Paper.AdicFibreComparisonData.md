## What changed

Filled `AlgebraicGeometry.Scheme.AdicFibreComparison.stageHeartMem` directly from the
published integral-image descriptions of the finite and common standard t-structures.
The upper and lower witnesses may be different integral objects: each is mapped through
the specified stage inclusion, and together they give common heart membership.

Reduced `AlgebraicGeometry.Scheme.AdicFibreComparison.scalarHeart` to integral heart
preservation. The rational proof first obtains one integral heart representative from
`pbc_localized_tstructure`, applies integral scalar extension, and composes the mapped
representative isomorphism with the inverse of `pbcScalarLocalizationIso`. Thus it uses
the actual scalar functor and the canonical localization comparison throughout.

Added the proof-only import `Sheaf.Paper.IntegralScalarHeart` and its single theorem
`AlgebraicGeometry.Scheme.pbcIntegralScalarHeart`. This is an integral assertion before
rationalization, including torsion inputs; it is strictly the finite-free integral part
of the argument, not the rational statement under another name. Its docstring gives the
complete coordinate/cohomology proof. Updated the owning DAG proof to match the Lean
assembly. No existing signature, definition body, target, or public import changes.

## Proved and sorry left

Original module: 2 holes.

- Proved `AlgebraicGeometry.Scheme.AdicFibreComparison.stageHeartMem` without new holes.
- Closed the original hole in
  `AlgebraicGeometry.Scheme.AdicFibreComparison.scalarHeart` by decomposition through
  the integral theorem and a complete rationalization argument.
- Added 1 hole:
  `AlgebraicGeometry.Scheme.pbcIntegralScalarHeart`, owned by
  `lem-per-adic-integral-scalar-heart` in `Sheaf.Paper.IntegralScalarHeart`.

The item now has zero direct holes; the delivered modules together have one. This is
one direct proof plus one decomposition, with net one hole closed. The remaining
integral assertion is true for zero objects, the empty scheme, identity embeddings,
ramified extensions, and integral torsion: finite free coefficient extension is exact,
so each case preserves concentration of cohomology in degree zero.

## No longer needed

No imports are removed and no modules are withdrawn. The existing public imports are
needed by the assertion structures or retained as published prerequisites. The new
proof-only import is used by `scalarHeart`.

`stageHeartMem` does not use the full theorem `perAdicCommonStageTruncations` of
`lem-per-adic-common-stage-truncations`: its conclusion follows already from the
published integral-image classes. That module remains publicly available through the
unchanged interface import, and the node remains a statement dependency of the
comparison-data definition; no global withdrawal is claimed.

The proof needs no normalized fibre comparison, rank construction, lattice stalk
comparison, or common-stage descent theorem. Those data structures remain untouched.

## Where the brief, the DAG or earlier work was wrong

The definition node listed the two named membership lemmas among its Lean declarations
but had empty `proof` and `proof_deps`. This packet records the actual proofs of those
membership claims. There is no statement dispute or change to the unit route.

`podCompletedScalarExtension_tExact` is formulated for the sf strict-tower integral
category and its completed-coefficient model, while this module uses the actual PBC
continuous coefficient category and its raw rationalization. It cannot simply be
applied by treating those categories or coefficient maps as identical. The new integral
node isolates precisely the finite-free calculation needed in the PBC model.

The common-stage proof initially required an explicit `change` to the chosen unique
t-structure before rewriting its defining halves; the final proof compiles with that
conversion and does not change any construction.

## New nodes

`lem-per-adic-integral-scalar-heart` states that the actual integral scalar functor
preserves the induced standard integral heart. Its two proof steps specify completed
finite freeness and the resulting exact cohomology calculation, with sources, existing
DAG dependencies, three recorded searches, and edge-case checks above. It is a strict
integral step of the scalar-heart proof; rational essential-image and localization
arguments are proved in the assigned module. No definition or statement repair was
made, so no change record or consumer adaptation is required.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
