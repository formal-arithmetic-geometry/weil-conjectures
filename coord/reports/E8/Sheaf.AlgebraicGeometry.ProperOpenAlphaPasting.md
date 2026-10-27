## What changed

Reduced all three theorems of `Sheaf.AlgebraicGeometry.ProperOpenAlphaPasting` to
three module-sheaf component calculations in new modules:
`ProperOpenAlphaVerticalModules`, `ProperOpenAlphaHorizontalModules`, and
`ProperOpenAlphaBaseChangeModules`. Each new statement is only the underlying
module-sheaf identity, strictly one part of the original five-clause theorem.

The item proves equality of the ordinary natural transformations by extensionality,
and obtains the complex, strict-tower, and tower-complex identities by congruence.
For the derived identities the proved transport helpers construct the actual finite
pasting expressions of exact tower functors. Their ordinary evaluations agree componentwise by the new
module-sheaf statements. Localization extensionality and the proved expression
factorization transport this equality. The intrinsic alpha cell is identified by
`alpha_eq_localized_singleAlpha`; beta and the specified compositors are identified
by their existing factorization lemmas. No faithfulness of derived evaluation is used.
All existing signatures, definitions, and public imports are preserved.
The component lemmas avoid unfolding module inverse-image and open-adjoint
constructions. Local opacity and explicit definitional normalization of the derived
functors keep the concrete transport checks small; no shared definition was changed.
Each new module-sheaf module also supplies its proved private tower and derived
consequences.
The tower proofs package the actual module functors and cells in native structures,
whose proof fields refer to the named module-sheaf theorems. Derived transport uses
explicit functor parameters and the existing localization compatibility lemmas.
Its functor types capture the public derived-category instances before the local
tower instance is installed. This avoids expensive conversions through the
localization construction. Every structure field is constructed explicitly; no
object is chosen from an unproved existence assertion.

The five delivery modules compiled individually in import order: the helper took
23.7 seconds, base change 13.9, horizontal 13.4, vertical 27.6, and the item 15.6.
The long-line warnings from that run have been corrected; all profiling and
diagnostic code has been removed.

## Proved and sorry left

Closed the three original holes:

- `AlgebraicGeometry.ProEtale.StrictTower.alpha_vertical_beforeDerivation`.
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_horizontal_beforeDerivation`.
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_baseChange_beforeDerivation`.

Added three strictly lower holes:

- `AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_vertical`, node
  `lem-cbc-proper-open-alpha-vertical-modules`.
- `AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_horizontal`, node
  `lem-cbc-proper-open-alpha-horizontal-modules`.
- `AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_baseChange`, node
  `lem-cbc-proper-open-alpha-base-change-modules`.

This is a decomposition: three original holes closed, three lower holes added,
net zero. The item itself has zero remaining holes. All transport helpers have
complete proofs, including `CategoryTheory.ExactDerivedPasting.exactPasting_congr`. The new statements include their complete restriction-detection
arguments and sources in their docstrings. Empty schemes, zero coefficients, and
identity opens satisfy these statements without an additional hypothesis.

## No longer needed

Removed the direct private import
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` from the item: restriction
detection belongs to the three new module-sheaf calculations. Removed its obsolete
parent `tool_uses` entry. The direct exact-derived-pasting proof import also moves
to the new helper module; the parent imports the three new component modules
with `import all` for their proved private transport consequences. This node and module remain needed by those lower proofs;
no claim of global pruning or withdrawal is made.

The original clopen-projector calculation is likewise needed only below the three
new nodes. The transport helpers use the already established localization specification of
intrinsic alpha instead of repeating that calculation. No public import was removed,
no module was withdrawn, and no source-library declaration was changed.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies state the open-unit normalization and clopen-projector
normalization, but do not state any of the three general module-sheaf pasting
calculations. Those were substantive glue in proof steps 4-6. They are now explicit
items; the functorial and localization transport is actual Lean code in proved helpers
used by the parent.
The unit route is unchanged.

## New nodes

`lem-cbc-proper-open-alpha-vertical-modules` isolates the module-sheaf vertical
calculation of parent steps 1-4, following Tag 0F7C and the recorded arbitrary-ring
restriction refinement.

`lem-cbc-proper-open-alpha-horizontal-modules` isolates the module-sheaf horizontal
calculation of parent steps 1-3 and 5, following Tag 0F7D and the same refinement.

`lem-cbc-proper-open-alpha-base-change-modules` isolates the module-sheaf cube
calculation of parent steps 1-3 and 6, following Tag 0F7F and the same refinement.

`lem-cbc-exact-derived-pasting-components` is a proved localization congruence
theorem, with private component and finite-expression calculations in its module.
It removes the unnecessary finiteness assumption on the indexing type: each word
and each expression is already finite.

Each node has its own module, complete natural-language proof, exact Lean signature,
source, dependency list, blueprint ancestry, and search record. The ringed open/closed
lemma is declared as a generic tool use for reader approval, preserving the parent's
previously approved use of that tool. No change record is needed: only the item,
its node, and these new modules and nodes are changed.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
