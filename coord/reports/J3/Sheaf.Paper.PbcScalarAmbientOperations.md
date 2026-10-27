## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.pbcScalarCompletionIso_exists`
with a complete reflection/adjunction argument in
`lean/Sheaf/Paper/PbcScalarAmbientOperations.lean`. Two private proved helpers
transport the source reflection Hom bijection through the specified scalar
adjunction and identify the actual completion unit with that Hom bijection.
The argument constructs the two component arrows, proves their inverse
identities, proves naturality, and proves uniqueness with the original unit
equation. All existing public declarations, signatures, attributes and definitions
are unchanged.

Added proof-only imports of `Sheaf.Paper.PbcScalarCompletedObjectComplete` and
`Sheaf.Paper.PbcScalarRestrictionComplete`. Their named statements isolate the
two concrete completeness inputs. Updated the item node's second proof step and
proof dependencies to the argument actually implemented. No other existing
module or node is changed. The unit route is unchanged.

Validation: both new lemma modules compiled through `lcompile.py` (51.2 and
51.1 seconds). The completed item compiled successfully in 12.7 seconds after
fixing explicit identity-functor simplifications. The sandbox node dependency
check found no cycles; the changed existing node fields are exactly `proof`,
`proof_deps`, and `proof_origin`. Every Lean line is at most 100 characters.
The first delivery preflight returned only two node-signature metadata errors:
`lean.statement` had expanded shared variables instead of the literal theorem
signature. Both records now contain the literal signatures. Added the separate
LeanSearch record requested by the search advisory; it found ordinary scalar
restriction/adjunction APIs, with no derived completeness theorem.

## Proved and sorry left

The item initially had three holes. One original hole is closed by decomposition:
`AlgebraicGeometry.Scheme.pbcScalarCompletionIso_exists`, node
`lem-pbc-scalar-ambient-operation-comparisons`. Its proof is complete from the two
strictly smaller completeness statements, with no sorry inside the construction.
This is a decomposition, not a net proof: one hole closed and two holes added;
the delivered modules contain four holes in total.

The two original holes retained in the item are:

- `AlgebraicGeometry.Scheme.pbcScalarDirectImageMap_isIso`, node
  `lem-pbc-scalar-ambient-operation-comparisons`.
- `AlgebraicGeometry.Scheme.pbcScalarCompletedExchange`, the same node.

The two added holes are:

- `AlgebraicGeometry.Scheme.pbcScalarCompletedObjectComplete`, node
  `lem-pbc-scalar-completed-object-complete`. Only asserts completeness of scalar
  tensor of a source completion output, with no natural comparison or unit equation.
- `AlgebraicGeometry.Scheme.pbcScalarRestrictionComplete`, node
  `lem-pbc-scalar-restriction-complete`. Only asserts completeness of exact scalar
  restriction of a complete target-coefficient object.

The new statements were checked mathematically for identity embeddings, ramified
extensions, zero complexes and the empty scheme. They impose no geometric or
constructibility hypotheses. The scalar/reflector proof uses their actual
statements, not completeness hypotheses as a replacement for the theorem.

## No longer needed

No existing import was removed and no whole module is pruned. The existing
public import of `PbcScalarStages` and private import of `PbcScalarTensor` remain.
In the item's second proof step, the former direct dependencies
`lem-weil-pbc-finite-free-strict-tower-transport`,
`lem-weil-pbc-finite-free-completion-transport`,
`lem-weil-pbc-constant-completion-equivalence`, and
`def-weil-pbc-completed-pullback` are replaced by the two completeness sublemmas,
`lem-weil-derived-scalar-extension-restriction-adjunction`, and
`lem-weil-pbc-ringed-topoi-module-adjunction`. Finite-free completion transport
remains part of the proof plan of the new concrete completeness steps; it is not
claimed globally unnecessary. Strict tower and constant completion machinery may
still be used by those steps or by the untouched direct-image/exchange proofs.

## Where the brief, the DAG or earlier work was wrong

The relevant general finite-free completion theorem is already proved, but its
small-site Koszul presentations and scalar model are not definitionally the actual
`PbcCompletedDerived` functors. Its restriction-completeness argument and its
finite-sum argument require transport through the normalized completed coefficient
presentation. The two sublemmas expose exactly these remaining concrete steps.
The comparison and its normalization are assembled from the existing actual
reflector instead of choosing an unspecified isomorphism. The existing
`WeilConjectures.purScalarModel` bridge in
`CompletedCoefficientPresentationTransport` cannot be imported here: that module publicly imports `PbcScalarExtension` and reaches this
item, so doing so closes an import cycle.

The node's old source path for `prop-weil-pbc-scalar-extension.md` is absent in the
latest blueprint snapshot. The mathematical source used here is the retained
finite-free transport argument recorded with Stacks Tags 099B and 0A0E in
`lem-weil-pbc-finite-free-completion-transport`; no unit statement or route changes.

## New nodes

`lem-pbc-scalar-completed-object-complete` records only target completeness of
scalar tensor of a source reflection output. Its plan uses the finite-free
completed coefficient basis, finite sums of complete complexes, scalar restriction
and the positive-power uniformizer relation. It owns
`lean/Sheaf/Paper/PbcScalarCompletedObjectComplete.lean`.

`lem-pbc-scalar-restriction-complete` records only preservation of completeness by
exact restriction. Its plan uses the restriction/Koszul comparison and the
unit-power criterion, transported to the actual intrinsic predicate. It owns
`lean/Sheaf/Paper/PbcScalarRestrictionComplete.lean`.

No statement or definition change record is needed: every existing public
signature and definition is preserved.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
