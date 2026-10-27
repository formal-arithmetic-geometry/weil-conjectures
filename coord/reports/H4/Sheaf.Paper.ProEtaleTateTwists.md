## What changed

Proved `AlgebraicGeometry.ProEtale.spIntegralTwistLevel_comparison` without changing
its statement, universes, public imports, or existing docstring. The
proof constructs the quotient scalar map, identifies the finite discrete pulled-back
coefficient with its constant sheaf, and applies an integer-versus-cyclic-ring tensor
comparison. Added proof imports of `Sheaf.Paper.FiniteDiscreteCondensedRing`,
`Sheaf.Paper.FiniteDiscreteSchemeRing`, and `Sheaf.Paper.ConstantZModScalarTensor`.

The new module `Sheaf.Paper.ConstantZModScalarTensor` proves
`AlgebraicGeometry.Scheme.constantZMod_scalarTensor` for every module sheaf over the
constant cyclic ring. It constructs both comparison maps and verifies both composites
on pure tensors, using module sheafification and the existing scalar-extension API.
The new lemma has no primality, invertibility, or finite-coefficient hypothesis.
Updated the finite-level comparison node's proof and proof dependencies to this route.

Kept ring instances local in the new proof. Profiling also identified repeated
completeness inference and unnecessary unfolding of completed integral limits.
Local priorities for existing limit/colimit projections and sheaf/abelian-group
completeness instances, plus local irreducibility after the integral transition
proofs, avoid that work. These attributes are not exported. Removed all profiling
options and selected synchronous elaboration (`Elab.async false`).

Three existing point-coefficient definitions now explicitly bind their already
available `IsTopologicalRing` proofs. These are proof-only changes: independent
`rfl` checks against all three original bodies compiled in 6.5 seconds.
See `coord/changes/H4-finite-coefficient-topological-ring-inference.md` for the
consumer audit and replayable preservation checks. No consumer adaptation is needed.
The item compiled cleanly in 34.5 seconds; the new comparison module also compiled
cleanly, with zero holes. Both have passed the per-file compile gate.

## Proved and sorry left

Baseline: two holes in the item module. Closed one:
`AlgebraicGeometry.ProEtale.spIntegralTwistLevel_comparison`
(node `lem-route-sp-integral-twist-level-comparison`).

One existing hole remains, unchanged:
`AlgebraicGeometry.ProEtale.spTwists_commonCover`
(node `lem-route-sp-twists-common-cover`). Its simultaneous integral, rational, and
algebraic-closure trivialization is separate from the finite-level comparison.

Added zero holes. The new theorem
`AlgebraicGeometry.Scheme.constantZMod_scalarTensor` and every private helper in its
module are proved. This is one hole closed, not a decomposition into new assumptions.

## No longer needed

The finite-level proof does not use `lem-sp-finite-tate-line-universal` or import
`Sheaf.Paper.FiniteTateLineUniversal`. Removed that node from this proof's dependencies
and obsolete top-level `tool_uses` entry. Its module reaches the item module, so the
planned import would also be cyclic. The replacement proves the needed tensor
comparison directly.

The internal/sectionwise equivalence and free-module Hom argument are no longer direct
steps of this theorem's proof. Their imports and nodes remain wherever the existing
constructions and other proofs use them. The sheaf tensor construction is used by the
new comparison lemma. No existing imports were removed, no module was withdrawn, and
no globally unused module is asserted here.

The new comparison also avoids `import all Sheaf.Paper.TateTwistLocallyFree`:
its additive-to-linear lift is proved directly from Mathlib's locally surjective
restriction equivalence and integer lifts of cyclic scalars. The generic proof
therefore does not require `lem-pur-torsion-sheaf-constant-module`; removed that
extra dependency from its new node. The actual root module and its existing
construction are retained by the item.

## Where the brief, the DAG or earlier work was wrong

The planned finite Tate universal-property import is unusable in this module:
`tools/import_direction.py may Sheaf.Paper.ProEtaleTateTwists
Sheaf.Paper.FiniteTateLineUniversal` reports a cycle through the latter's dependencies.
The elementary sheafified integer-tensor argument supplies the comparison without
changing the mathematical statement or the unit route. No statement dispute or
forced adaptation is involved.

## New nodes

`lem-sp-constant-zmod-scalar-tensor` is attached to the proved theorem
`AlgebraicGeometry.Scheme.constantZMod_scalarTensor` in the new module
`Sheaf.Paper.ConstantZModScalarTensor`. It records the finite-level tensor comparison,
its two inverse maps, source, edge cases, and LeanSearch/Loogle/LeanFinder/source searches.
It inherits the finite comparison's chapter and unit. The proof-instance definition
changes are documented in the change record named above; existing statement
signatures and mathematical objects are preserved.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
