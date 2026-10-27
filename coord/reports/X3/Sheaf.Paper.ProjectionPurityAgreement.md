## What changed

Replaced the final hole in `Sheaf.Paper.ProjectionPurityAgreement` by an assembly.
The assembly chooses an existing etale finite-Tor presentation, evaluates both
intrinsic unique specifications in that presentation and applies
`projection_intrinsic_presentation`. That lemma is the realization of
`projection_presentation_coordinate`. The coordinate lemma rewrites the inverse
diagonal orientation by the unit orientation comparison and applies the tensor
equation and the existing ordered-integration transpose theorem. It then cancels the
invertible exceptional coordinate map. The target statement is unchanged.

Extracted the coordinate prefix verbatim into
`Sheaf.Paper.ProjectionPurityCoordinates`, publicly reexported by the item.
All existing public names, signatures, attributes and definition bodies are retained;
no consumer needs adaptation. The change record lists every transitive consumer.

`Sheaf.Paper.ProjectionUnitIntegration` constructs the ordinary unit counit mate
and transports it between the two recursive affine towers by a unique HEq
specification. It proves that the inverse diagonal orientation equals this mate.
`Sheaf.Paper.ProjectionTensorIntegration` states the coefficient tensor, site
transpose and adjacent Tate-exponent comparison, and proves the two assembly
lemmas from it.

(Reviewer, 2026-10-26: the delivered version left `projection_presentation_coordinate`
and `projection_intrinsic_presentation` with `sorry`. The item then reduced only to
the latter, which is the item in one presentation. The reviewer proved both lemmas.
The statement of `projection_intrinsic_presentation` now fixes the structures over k
by aY, as the item installs them. Before, it quantified over arbitrary `Over`
instances, under which `smoothPurityMap` uses another structure map.)

## Proved and sorry left

The original hole `WeilConjectures.PurityFiniteSetting.projection_purity_agreement`
(node `lem-pur-projection-purity-agreement`) is replaced by a complete assembly.
`projection_diagonal_unit_integration` (`lem-pur-projection-unit-integration`),
`projection_presentation_coordinate` (`lem-pur-projection-presentation-coordinate`) and
`projection_intrinsic_presentation` (`lem-pur-projection-intrinsic-presentation`) are proved.

The one remaining new hole is
`WeilConjectures.PurityFiniteSetting.projection_tensor_integration`
(node `lem-pur-projection-tensor-integration`). It is a tensor/site/coefficient
coordinate comparison for the independently constructed unit integration mate,
strictly part of the original argument. It has a complete sourced natural-language
proof and is the entire body of its public theorem in a separate module. The upstream
`ordered_integration_transposes` and the diagonal orientation statements are still
`sorry` in the library.

No definition contains a hole.

## No longer needed

No module is withdrawn. Existing public prerequisites remain publicly reexported.
The main assembly no longer directly uses
`lem-pur-affine-diagonal-integration-orientation` or
`lem-pur-affine-coefficient-counit-normalization`: its two extracted steps specify
the missing comparisons precisely. The latter remains a prerequisite of the
new tensor step; the former's diagonal/DNC content is retained by the existing
normalized diagonal orientation and its identity-chart specialization.

Proof imports for constructible origin, comparison Tor amplitude, and ordered
integration remain necessary for the presentation-independence proofs. The
smooth-morphism import moves with the verbatim coordinate prefix. The split
statement does not import AffineCoefficientCounitNormalization, TensorTraceTranspose
or FiniteSiteCounitProjectionTransport: they remain its planned proof dependencies
in the DAG, rather than unused imports in its current sorry body.

## Where the brief, the DAG or earlier work was wrong

The short four-step DAG assembly omits non-definitional identifications between
the normalized diagonal orientation and its ordinary counit representative,
between the two recursive affine tower/projection pairs, and between the adjacent
annihilating Tate exponents. Existing theorem statements do not themselves supply
one equation already in the item's exact coordinates. The new steps expose these
comparisons, while preserving the diagonal/DNC and ordered-integration unit route.

There are no statement disputes, target changes, consumer adaptations, arbitrary
existential choices of data, or changes under `lean/WeilConjectures`.

## New nodes

- `def-pur-projection-purity-coordinates`: verbatim existing coordinate prefix,
  now a prerequisite for separately stated comparison steps.
- `lem-pur-projection-unit-integration`: equality of the inverse diagonal
  orientation with the independently constructed ordinary coefficient-unit counit
  mate after exact site comparison and comparison-unit coordinates.
- `lem-pur-projection-tensor-integration`: the tensor/site/Tate coordinate
  comparison, without any diagonal orientation or smooth purity map in its statement.
- `lem-pur-projection-presentation-coordinate`: the fixed-presentation coordinate equation.
- `lem-pur-projection-intrinsic-presentation`: transport of the smooth map to that presentation.

The nodes cite the current blueprint model paragraph and its canonical
reassociations. LeanSearch, LeanFinder/Loogle, source grep and imported blueprint
searches found no matching coordinate compatibility; generic adjunction and
ordinary tensor-trace identities were inspected. Edge cases checked: d=0, K=0,
empty Y, arbitrary disconnected Y, and ramified levels without divisibility.

Change record: `coord/changes/X3-projection-purity-coordinate-extraction.md`.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
