## What changed

Completed three proofs in `Sheaf.AlgebraicGeometry.CartierPairTensorAddition`.

`cartierPairTensor_geometry` now constructs ideal multiplication globally using
the tensor-bilinear universal property and the kernel of the product-ideal quotient.
On a common affine refinement it sends the tensor of ideal generators to their
product; the local free-generator criterion makes it an isomorphism. The existing
Cartier product and ideal support lemmas give invertibility, the union of supports,
the complementary-open equation, and the principal product equation. Comparing
the two evaluation isomorphisms and using full faithfulness of tensoring by an
invertible object constructs the dual isomorphism. Evaluation of the transpose
sections proves its specified-section equation. All intermediate helpers are
private and proved.

`cartierPairRestriction_square` follows degreewise from presheaf composition and
terminal-object uniqueness. The proved private helper `cartierPairRestriction_map`
establishes commutation with coefficient-complex maps by functoriality of the
actual shifted mapping cone. Applying homology proves the first clause of
`cartierPairTensor_naturality`; connecting-map naturality applied to a morphism of
the supplied split relative rows proves the second clause in every integer degree.

Added private proof imports for the ideal-locality API, tensor sections, the
sheaf tensor-bilinear universal property, Cartier products, and invertible tensor
cancellation. Removed unused private imports listed below. Public imports,
existing declaration signatures, definitions, and the unit route are unchanged.
The node records the implemented geometry and naturality arguments; its other
proof steps remain the existing plans. No other module is adapted.

## Proved and sorry left

Closed 3 of the original 5 holes:

- `AlgebraicGeometry.Etale.cartierPairRestriction_square`.
- `AlgebraicGeometry.Etale.cartierPairTensor_geometry`.
- `AlgebraicGeometry.Etale.cartierPairTensor_naturality`.

Added 0 holes and split off 0 statements. The two remaining original holes are:

- `AlgebraicGeometry.Etale.cartierPairTensor_frames`.
- `AlgebraicGeometry.Etale.cartierPairTensor_extensions`.

Both retain their existing statements and complete proof plans under
`lem-pur-cartier-pair-tensor-addition`. This is a partial proof delivery of a
module with several holes, not a decomposition. The geometry imposes no
reducedness, disjointness, or nonempty-open hypothesis. The restriction and
naturality proofs allow empty and equal opens and all integer degrees.

## No longer needed

Removed these unused private proof imports:

- `Sheaf.AlgebraicGeometry.CartierComplementFrame`.
- `Sheaf.AlgebraicGeometry.RelativeTorsorForgetNormalization`.
- `Sheaf.AlgebraicGeometry.RelativeTorsorClassNaturality`.
- `WeilConjectures.SixFunctors.OpenClosed.Exact`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.CategoryTheory.PushoutShortExactSequence`.
- `Sheaf.CategoryTheory.YonedaBaerExistence`.
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.

The implemented restriction/naturality argument does not need these nodes, so
their proof-dependency and corresponding tool-use entries are removed:

- `lem-amb-relative-torsor-class-naturality`: direct naturality of the complex
  maps suffices; the statement does not assert a coefficient-change formula
  for the torsor classifier.
- `lem-weil-pbc-injective-resolution-ses`: the statement already supplies split
  coefficient-complex rows, so no horseshoe construction is needed.
- `lem-weil-pbc-injective-resolution-lift-exists`: the statement supplies each
  coefficient-complex map, so no resolution lift is needed.

No module is withdrawn. Dependencies still cited by the unfinished frame and
extension steps remain in the node. In particular, removing an unused Lean import
here does not claim those remaining mathematical steps are proved or unnecessary.
The ordinary `GmPicard` tensor-class theorem omits the specified-section and
relative-class clauses, so it does not replace the remaining frame theorem.
The tensor-bilinear universal-property node is now explicitly recorded as used
by the geometry proof.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The node's original naturality plan invoked
horseshoe resolutions and augmentation-preserving lifts, whereas the Lean
statement already supplies degreewise splittings and coefficient-complex maps.
Its proof can therefore apply the existing relative short-exactness theorem and
Mathlib's connecting-map naturality directly. The geometric argument implements
the original local multiplication plan, but uses categorical evaluation and
invertible tensor cancellation for the dual and section identities. No claim is
made that the framed-torsor or extension-addition steps are complete.

On resumption after the launcher's queue pause, the budget metadata had changed
from start identifier `1792749375.851804` to `1792773481.4218771`; this was not
edited by the worker. The first delivery attempt timed out in its compile and
pushed nothing. Profiling identified expensive inference in the final tensor
evaluation application; supplying its modules, sections and inclusions explicitly
preserves the proof and reduces that inference work. The full profiling compile
then passed in 24.7 seconds, with that application taking 965 milliseconds.
Profiling options occur only in scratchpad files, outside the delivered module.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
