## What changed

Proved `AlgebraicGeometry.Scheme.ProjectionRestriction.localTensorSquare` with its
original statement, binders, universes and public import unchanged. The proof
works directly with the independently sized pro-étale sites in `Global` and
`Local`, rather than transporting them into a different ringed-square package.

Two new modules contain proved supporting arguments:

- `Sheaf.Paper.RingedProjectionLocalPullbackNormalization` constructs
  `localOrdinaryPullbackSquare` by the actual inverse mates equivalence and proves
  `localPullbackNormalization` on every complex. Its proof uses the existing
  `derived_unit_cochain`, naturality along a K-injective resolution, and the given
  `mate_counit` equation. No arbitrary data are chosen from an existence theorem.
- `Sheaf.Paper.RingedProjectionLocalOrdinaryTensorSquare` proves
  `localOrdinaryTensorSquare` from the inverse-mate unit law, the supplied
  sectionwise identity and pure-tensor normalizations. It privately imports the
  proved pure-section calculus in `CochainTensoratorExistence`, whose site object,
  morphism and coefficient universes are independent.

The item module proves the signed total-complex square by summand extensionality,
pastes the four representative equations in a private lemma over arbitrary
module functors, cancels their factorization
isomorphisms, and uses resolving-pair faithfulness to descend to arbitrary
inputs. Both new supporting modules and their DAG nodes are included. No existing
module other than the assigned item was edited. There is no shared-interface or
definition repair and no forced adaptation.

Validation: the three delivered modules compile individually within 60 seconds.
The final item compile, with profiling removed, took 58.1 seconds and reported no
warnings or errors. Keeping the four-model algebra abstract reduced the previous
104-second concrete calculation to an accepted compile. All delivered lines are
at most 100 characters, and the original public theorem signature is identical.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Scheme.ProjectionRestriction.localTensorSquare`.

Added zero holes. The new theorems
`AlgebraicGeometry.Scheme.ProjectionRestriction.localPullbackNormalization` and
`AlgebraicGeometry.Scheme.ProjectionRestriction.localOrdinaryTensorSquare`, the
constructed ordinary mate, and every private helper have complete Lean bodies.
There is no `sorry` in any delivered Lean file. This is a proof, not a further
decomposition into unproved intermediate statements.

## No longer needed

No original Lean import was removed: the item initially publicly imported only
`RingedProjectionRestrictionData`, which it still needs.

The following planned proof dependencies are not used by this proof and are
removed from this item's `proof_deps` and proof-step `uses`:

- `lem-weil-pbc-ringed-slice-pullback-mate-normalization`
  (`Sheaf.Paper.RingedSlicePullbackMateNormalization`): its shared small-site
  presentation is unnecessary; the canonical cochain unit and the supplied
  K-injective normalization prove the needed identity directly.
- `lem-weil-pbc-localize-ringed-site-morphism`
  (`Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`): no construction of a localized site
  morphism is needed, since the theorem takes its actual `Local` data as input.
- `lem-weil-pbc-ringed-square-tensor-compatibility`
  (`Sheaf.Paper.RingedSquareTensorCompatibility`): the tensor-square calculation
  is proved directly from the four supplied representative equations.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
  (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`): no existence theorem for a
  derived tensor comparison is needed; the four comparisons are already fields.
  The lower constructions exported through `RingedProjectionRestrictionData`
  remain available and are not withdrawn.

These are removals from this node's planned proof route, not claims that these
modules are unused everywhere. No module or declaration is withdrawn. The unit's
statement and realized proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and no disputed statement was found.
The supplied generic proof dependencies use a different ringed-site presentation
and shared universe sizes; constructing transports is avoidable. The direct
argument also shows that pullback normalization holds on all complexes, so no
extra total-tensor K-flatness lemma is required for the normalization at the total
complex. The ordinary argument uses no nonzero-ring, flatness or nonzero-module
hypothesis and includes the degenerate cases.

The blueprint ancestor helper could not trace `created.item` recorded as a Lean
module name and printed a `None` ancestor. The existing item's explicit blueprint
ancestry is present and was preserved for the two new nodes, with the item added
as their nearest intermediate node. Searches of the current blueprint found no
separate statement of either supporting theorem. The paper/unit route is kept.

## New nodes

`lem-weil-pbc-ringed-projection-local-pullback-normalization` records the constructed
ordinary inverse mate and its proved cochain normalization. It contains no tensor
comparison hypothesis or conclusion.

`lem-weil-pbc-ringed-projection-local-ordinary-tensor-square` records the proved
ordinary module tensor equation. It contains no complexes, localization or
resolving assumptions. Both nodes have complete proof plans, the three kinds of
search, source citations and the same chapter/unit as the item. No change record
is needed because no existing public interface changed.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
