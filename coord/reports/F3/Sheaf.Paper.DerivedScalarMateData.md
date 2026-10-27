## What changed

Prove `AlgebraicGeometry.Scheme.DerivedScalarMate.derivedTensorIso_existsUnique` in
`Sheaf.Paper.DerivedScalarMateData`. Construct the comparison on flat-term K-flat
representatives from the prescribed scalar counit, the existing ordinary comparison,
and a coefficient resolution. The proved fixed-factor tensor comparison identifies
its normalization for every coefficient resolution. Fully faithful restriction to
resolving representatives descends the natural isomorphism. Cancellation in the
normalization equation proves uniqueness.

Add proved private helpers, with proof imports for the existing fixed-factor
comparison, resolving-representative restriction, K-flat fixed tensor, and the
site/monoidal tensor identification. Update the attached node's proof and dependencies.
The existing public signatures, definitions, attributes and public imports are retained.
No source-library file or other existing module is changed. A private equation for
the ordinary component lets its pure-tensor calculation use that equation without
expanding the component construction repeatedly. After profiling and replacing slow
conversions by explicit component equations, extract the already proved ordinary
comparison and its definitions to `Sheaf.Paper.DerivedScalarTensorOrdinary`. The item
publicly imports it, preserving all declaration names and definition bodies. The
ordinary comparison, fixed-coefficient tensor calculation, scalar comparison on
representatives, and descent now compile separately.
The new `representativeScalarTensorIso` is fully proved; it gives the natural
comparison on flat K-flat complexes, before descent or uniqueness on the derived
category. The assigned theorem uses it and proves descent and uniqueness.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.DerivedScalarMate.derivedTensorIso_existsUnique`
(node `lem-sfb-derived-scalar-tensor-identification`), the item's one original hole.
Added: none. Remaining holes in this delivery: none. This is a proof, not a decomposition.

Validation: all four sandbox modules compile in import order with `lcompile.py --all`.
The final measured checks were 38.1 seconds for the fixed-coefficient tensor module,
18.3 seconds for the scalar representative module, and 26.7 seconds for the item;
the ordinary module also passed (34.8 seconds in its preceding full check). Direct
consumers `DerivedScalarMateExactStructures`, `DerivedScalarMateProjectionNormalization`,
and `DerivedScalarMateThickLocus` all compile unchanged against the delivery (8.9,
8.7 and 11.3 seconds). Their temporary copies have been removed. Delivery preflight
is run by the required delivery command.

## No longer needed

No public import is removed and no module is withdrawn. Move the private imports
`Sheaf.Algebra.Homology.ExtensionTensorComparisonIndependent` and
`Sheaf.SecSmoothPurity.ModuleTensorGenerators` from the item into the extracted
ordinary-comparison module, where their proofs are used. The fixed-factor and K-flat tensor proof imports move into the representative
comparison module. All added proof imports are used. The extracted module is a fully proved dependency, not a new obligation.

Remove these direct proof-plan dependencies from this node:

- `lem-pur-derived-change-of-rings`: the actual selected scalar functor and its
  invertible K-flat counit are supplied by `FourCorners` and `AdicCoefficientDatum`.
  The newly attached ordinary-module interface is not invoked.
- `lem-weil-pbc-ringed-projection-mate-exact`: no projection mate, triangulated
  closure or shift calculation is required to identify restricted scalar extension.
- `lem-weil-pbc-site-derived-tensor-descent`: its fixed-factor specialization and
  the resolving-representative full-faithfulness theorem provide the precise APIs
  needed here. The generic tensor-descent theorem remains a transitive dependency
  of the fixed-factor API; this delivery makes no whole-library pruning claim.

## Where the brief, the DAG or earlier work was wrong

The original sketch correctly described the construction, but did not identify the
already proved `proEtale_fixed_tensor_representative_comparison` interface. It supplies
the normalization at an arbitrary coefficient complex without any flatness assumption
on that coefficient. No mathematical statement repair is needed. The ordinary extraction is required
only after profiling identified the combined file as exceeding the compilation limit.

## New nodes

- `lem-sfb-scalar-tensor-ordinary-normalization`, realized by
  `Sheaf.Paper.DerivedScalarTensorOrdinary`: the pre-existing, fully proved ordinary
  comparison and its supporting definitions. No new `sorry` is introduced.
- `lem-sfb-scalar-tensor-representative-normalization`, realized by
  `Sheaf.Paper.DerivedScalarTensorRepresentatives`: the fully proved construction
  and normalization before descent. This adds zero holes; the final descent and
  uniqueness proof stays in the assigned module.
- `lem-sfb-fixed-coefficient-tensor-representative-normalization`, realized by
  `Sheaf.Paper.DerivedFixedCoefficientTensorComparison`: the fully proved tensor
  calculation before the scalar counit. It handles arbitrary maps to the
  coefficient complex and adds zero holes.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
