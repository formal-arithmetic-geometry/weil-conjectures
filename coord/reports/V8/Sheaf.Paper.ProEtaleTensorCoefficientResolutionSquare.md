## What changed

Filled the proof of
`AlgebraicGeometry.Scheme.proEtale_tensor_coefficient_resolution_square`
without changing its statement, any public definition, or any public import.
All helper lemmas are proved. Four comparison lemmas were extracted into new
modules after the error-free monolithic proof took 92 seconds to check. The original
public definitions, theorem statement, and public imports remain verbatim.

The published pro-etale descent data give the chain square and preservation of
flat-term K-flat representatives. The existing total-tensor theorem gives flatness
and K-flatness of all top complexes. The fixed-K-flat tensor theorem gives both
vertical quasi-isomorphisms. The defining characterization of the canonical
comparison gives the top derived identity.

For independence, tensor with fixed P is localized directly. Full faithfulness of
restriction to flat representatives extends the specified representative comparison
and normalizes it on every flat H. Naturality then identifies every alpha, for every
allowed resolution and inverse witness, with the same component of that natural
isomorphism. The final identity is a complete cancellation calculation using the
localized chain square, epsilon naturality, tau naturality, and bifunctoriality.
This retains arbitrary unbounded complexes and arbitrary, possibly nonflat, N.

The server compiled all five modules without errors or warnings. Explicit localization
inversion witnesses and local reduction attributes avoid expensive instance search;
no public reduction attribute was changed.

Updated the item's existing DAG node to describe this route. Four proved helper
statements and their nodes were added; no definition, axiom, or split-off hole was
introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proEtale_tensor_coefficient_resolution_square`
(node `lem-sp-proetale-tensor-coefficient-resolution-square`).

The four new proved declarations are
`AlgebraicGeometry.Scheme.proEtale_fixed_tensor_representative_comparison`,
`AlgebraicGeometry.Scheme.proEtale_resolution_sigma_naturality`,
`AlgebraicGeometry.Scheme.proEtale_resolution_representative_square`, and
`AlgebraicGeometry.Scheme.proEtale_resolution_derived_square`.

Original holes: 1. Holes closed: 1. Holes added: 0. Holes remaining in the delivery: 0.

## No longer needed

Removed these private imports from the item:

- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.TensorPullbackRepresentativeDescent`

The corresponding original direct proof dependencies are no longer directly used:
`lem-pur-cochain-pullback-tensor-coherence`,
`lem-pur-proetale-inverse-image-tensor-comparison`,
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-trf-site-one-sided-tensor-normalization`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`lem-weil-pbc-tensor-comparison-descent-representatives`.
Some remain transitive dependencies of the published comparison and descent data;
this delivery makes no claim that their modules are globally unreachable.
The six corresponding obsolete entries in the node's `tool_uses` were removed,
preserving the order of the three retained entries.
The direct replacement interfaces are the already proved pro-etale tensor descent
data, fixed-K-flat tensor theorem, K-flat resolution theorem, resolving-representative
whiskering theorem, and Mathlib localization universal property.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The original plan's homotopy-level one-sided
normalization interface needs substantial transport to use the item's arbitrary
cochain-level tensor model. Localizing the fixed tensor and extending its specified
comparison by full faithfulness proves the same normalization directly, without
adding an unproved statement. The unit record has no realized nodes or prescribed steps
for this auxiliary lemma, and its coefficient-comparison route is preserved.

The existing fixed-K-flat tensor and resolving-representative whiskering results
are used as tools from the proper-base-change unit: they provide exactly the
quasi-isomorphism preservation and restriction assertions needed by the original
localization argument. Only the six obsolete direct-dependency tool approvals
listed above were removed;
no tool approval was added, replaced, or reordered.

## New nodes

- `lem-sp-fixed-tensor-representative-comparison`, in
  `Sheaf.Paper.ProEtaleFixedTensorRepresentativeComparison`: the fully proved
  natural comparison for tensor with one fixed flat-term K-flat representative.
- `lem-sp-resolution-sigma-naturality`, in
  `Sheaf.Paper.ProEtaleResolutionSigmaNaturality`: the fully proved chain square
  at any coefficient map, with no flatness or quasi-isomorphism assumptions.
- `lem-sp-resolution-representative-square`, in
  `Sheaf.Paper.ProEtaleResolutionRepresentativeSquare`: the fully proved defining
  representative square for the specified canonical derived comparison.
- `lem-sp-resolution-derived-square`, in
  `Sheaf.Paper.ProEtaleResolutionDerivedSquare`: the fully proved derived equality
  from the specified forward maps, representative square, and naturality.

These isolate self-contained parts of the proof for kernel checking; none is the
full item under another name, and none contains a hole. No change record is needed:
no existing definition or statement changed and no other existing module was edited.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
