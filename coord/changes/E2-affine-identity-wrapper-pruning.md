# AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity

## Reason

The assigned Sheaf module has zero declarations and zero holes: it only publicly
re-exports the complete adopted upstream identity theorem. Its only mathematical
consumer, the upstream normalized-edge theorem, already imports the upstream
identity module directly. Withdraw the unused compatibility path and correct the
consumer node to record that actual proof. This is pruning, with no proof credit
claimed for either existing theorem.

The identity theorem constructs the natural transformation from the sheaf edge,
the supplied comparison, and the tilde/Gamma counit; the adjunction triangle and
comparison factorization prove normalization. The consumer obtains that result,
eliminates the representative object equality, and uses Iso.ext to reduce its
isomorphism to the identity. Both existing complete proofs are preserved verbatim.

## Old

The compatibility module is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity

/-! # Identity-representative affine cohomology edge normalization

The adopted upstream module provides the proved normalization theorem. Re-export it
at the existing module path, using the canonical cohomology coordinates and their
explicit sheaf universes.

Source: Stacks Project, perfect.tex, Tags 0AVW and 08D4.
(blueprint: lem-pc-affine-pushforward-cohomology-edge-identity). -/

@[expose] public section
```

The normalized-edge node's proof described an inline construction, although its
recorded upstream theorem actually calls the identity theorem. Its old direct
proof dependencies were:

- def-pc-affine-base-change-tilde-coordinates
- def-pc-affine-pushforward-comparison-coordinates
- lem-pc-affine-derived-pushforward-sheaf-edge
- lem-weil-pbc-affine-tilde-gamma-adjunction

## New

Withdraw only lean/Sheaf/Algebra/Homology/AffinePushforwardCohomologyEdgeIdentity.lean
through deleted.txt. The landing tool writes an empty module. The existing
canonical provider remains
AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity in
WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity.
Its source, signature, visibility, attributes, public and private imports, proof,
and explicit sheaf universes do not change. The quarantine archive is preserved.

The consumer node now records its actual two-step proof and its direct proof
dependency lem-pc-affine-pushforward-cohomology-edge-identity. The consumer's Lean
attachment and verbatim signature are retained; existing is corrected to true.
All former mathematical dependencies remain reachable through the identity node
and its comparison-coordinate dependencies; every stmt_deps list is unchanged.
The identity node keeps all its proof steps and dependencies, with notes updated
to document withdrawal of the unused compatibility path.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity | E2 | Withdraw the unused re-export; no mathematical declaration is removed. |
| WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity | unclaimed | Complete canonical provider preserved verbatim. |
| WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeExists | unclaimed | Complete canonical consumer preserved verbatim; its node now records the actual identity-theorem application. |

The downstream query reports zero modules and zero declaration uses downstream
of the Sheaf path. Searches of lean/Sheaf, lean/WeilConjectures, and quarantine
find no current or archived importer of that path. The current source has one
direct user of the identity declaration: the canonical normalized-edge theorem.
There is no existing DAG dependency on the identity node: the consumer's source
uses it, so that missing edge is added in this packet. Historical created.item
and blueprint.from fields are provenance, not dependencies. Neither node occurs
in a unit realized list; the enclosing unit route is unchanged. No target or
definition changes, and no forced consumer adaptation is needed.

Validation: recompile the complete canonical identity proof and the complete
canonical consumer in scratch through lcompile.py; print their axioms. The
consumer has only propext, Classical.choice and Quot.sound. The identity result
and its component proofs are checked in the same way. Scratch files are outside
lean/ and are not part of the packet.

## Status

landed 20261020T162303-L-3586464 2026-10-20 (merge of deliver/E2/Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity)
