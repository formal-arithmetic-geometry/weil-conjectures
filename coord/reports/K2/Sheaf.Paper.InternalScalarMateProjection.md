## What changed

Replace the single sorry in
`AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_mate_projection`
with the formal mate/counit argument from the recorded normalization statements.
The projection equation is proved by injectivity of the geometric adjunction Hom
equivalence, the mate-counit identities, the normalized pull/tensor equation, and
bifunctoriality. Derived scalar restriction reflects isomorphisms by its homology
comparison and ordinary restriction. Naturality comes from the naturality of the
published right-adjoint projection map and the coefficient postcomposition.

The fixed section equation uses `ModuleRingedComparison.projection_comparison`,
the equality of the published and generic derived tensor comparison, and the
coefficient-modified adjunction transpose. In particular the scalar pushforward
comparison is identified with the fixed derived pushforward comparison by
`scalarSectionPushMate_eq`, not by definitional reduction. Existing public
signatures, definitions, public imports and visibility stay unchanged.

Restore the absent modules `InternalScalarTensorPullNormalization` and
`InternalScalarRestrictionMateNormalization` from their existing DAG signatures.
They were split off by the previous J3 packet, whose route remains in the node,
but their source files and the item's proof were reverted. Each restored file
contains its named theorem with the recorded source and complete proof in words.
The restriction-mate statement is proved by adapting the existing argument in
`NormalizedScalarRestrictionPush`: ordinary scalar-unit compatibility, derived
counit factorization, uniqueness of left-derived transformations, and the iterated
mates identity. Its generic calculation helpers are reused directly; that downstream
module itself is not imported, so the dependency remains acyclic.
No new mathematical node or duplicate normalization statement is introduced.
The local proof commands are documented in
`coord/changes/K2-internal-scalar-mate-proof-context.md`.

## Proved and sorry left

One original hole is closed in the item:
`AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_mate_projection`
(node `lem-sfb-internal-scalar-mate-projection`). Its proof is complete relative
to the imported normalization lemmas. There are no sorries in the item module.
All new private helpers are proved. The restriction-mate module has a clean
single-file compile (29.7 seconds); the tensor statement also compiled. The main theorem module compiled in 47.8 seconds; its single unused-simp
warning was removed. Final validation is performed by the delivery tool on the
complete packet.

One smaller hole is restored relative to the current source tree, as the entire
proof of its named public theorem:

- `AlgebraicGeometry.ProEtale.QuotientChange.scalar_tensor_pull_normalization`,
  node `lem-sfb-internal-scalar-tensor-pull-normalization`, in
  `Sheaf.Paper.InternalScalarTensorPullNormalization`.

The restored `AlgebraicGeometry.ProEtale.QuotientChange.scalar_restriction_mate_normalization`
(node `lem-sfb-internal-scalar-restriction-mate-normalization`) has a complete proof.
This is a decomposition: one original upper hole closed and one lower hole restored
(net zero among these declarations). No closure-wide progress is claimed. The
remaining statement is only the pull/tensor square. It does not state the projection
identity, the section identity, reflection of isomorphisms, or naturality. These
remaining conclusions are combined by actual Lean proofs in the item.

Both normalization statements allow identity coefficient and scheme maps, zero
coefficient rings, empty schemes, nonflat scalar extensions, and arbitrary
unbounded complexes. The K-flat argument resolves the coefficient independently;
it does not assume that the degree-zero coefficient is K-flat. Neither data nor
any definition contains sorry, and no axiom is added.

## No longer needed

Remove the private direct imports
`Sheaf.CategoryTheory.InternalSectionTensorComparison`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Paper.KFlatRingedToposPullback`,
`Sheaf.Paper.RingedTopoiTensorComparisonData`, and
`Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients`.
Those tools belong to the separate pull/tensor normalization argument. They
remain in its recorded proof dependencies; this packet does not claim that they
are pruned from the targets' closure. The section calculation uses the existing
fixed comparison theorem rather than rebuilding the comparison from resolutions.

No module or node is withdrawn and no unit statement or step is bypassed.
The item's existing six-step proof route is preserved; its section step now explicitly
records `lem-pd-section-derived-tensor-normalization` and
`lem-sfb-scalar-geometric-exchange-rectangle`, whose proved equalities are used. The restriction-mate
normalization's dependencies are updated to the ordinary-unit and derived-counit
calculations actually used; its former planned direct use of
`lem-weil-pbc-ring-sheaf-change-adjunction`, `new-comap-upper-star-iso-mate`,
`lem-pc-kflat-resolution`, and `lem-sfb-internal-scalar-pullback-normalization`
is unnecessary for this proof. Their modules are not withdrawn.
No existing public import is removed. The original scalar-pullback normalization
module remains necessary for its public interfaces; its existential theorem is
not used to replace the given normalized data by chosen witnesses.

## Where the brief, the DAG or earlier work was wrong

The DAG records two normalization modules that are absent from the current Lean
tree, despite the item already citing their nodes. Restoring their exact recorded
signatures makes the existing plan usable without inventing replacements.
The older J3 report and compiler log identify a failed section comparison: the
mate-based `scalarSectionPushComparison` is propositionally identified with
`derivedPushComparison`, so simplifying its definition is insufficient. The
proof now uses the published normalization equality explicitly.

The shortest-route searches used the wrapper's LeanFinder query for the scalar
mate/projection identity (only constituent ordinary adjunction hits), Loogle
`"mateEquiv", "projection"` (no hits), and grep for
`rightAdjointProjectionMap|mateEquiv_counit` (constituent mate identities).
Repository searches found the fixed section projection comparison, the
proved homology argument for reflection, and the downstream normalized restriction
proof, whose independent argument is reused without importing its consumer. No existing target
statement, definition meaning or source-library declaration is changed.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
