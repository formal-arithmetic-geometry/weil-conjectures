## What changed

Filled `AlgebraicGeometry.Scheme.pbc_adic_flat_iff_supplied_model_flat` in
`lean/Sheaf/Paper/AdicSuppliedModelFlatCriterion.lean`, preserving its signature,
visibility, public imports, and existing docstring. Added proof imports and proved
private helpers for isomorphism invariance, preservation, and descent of flatness.
The reverse implication uses the uniform local models already supplied by the
constructible-complete hypothesis.

Added `lean/Sheaf/Paper/AdicSuppliedModelReconstruction.lean` with the proved theorem
`AlgebraicGeometry.Scheme.pbc_suppliedModel_reconstruction`. It identifies any supplied
common model with the inverse image of the complete ambient object. The proof uses
compatible levelwise isomorphisms of the completed-coefficient reduction sequences
and uniqueness of their Roos derived limits. Private helpers prove preservation of
products, completeness of the model, and compatibility of the ordinary and derived
coefficient comparisons with quotient transitions. No existing definition or
statement was changed; no source-library file was changed.

Validation: `lcompile.py` compiled the reconstruction module without warnings
(56.0 seconds in the combined check) and compiled the final item without warnings
(8.6 seconds). Both use the normal compile limits.

Updated the item's node proof and dependencies to this route and added the
reconstruction node. The unit `sk-rem-rest` has no realized proof steps to replace.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.pbc_adic_flat_iff_supplied_model_flat`
(node `lem-weil-pbc-adic-flat-iff-supplied-model-flat`): 1 of 1.

The new theorem `AlgebraicGeometry.Scheme.pbc_suppliedModel_reconstruction`
(node `lem-weil-pbc-supplied-model-reconstruction`) and all its private helpers are
proved. Holes added: 0. Sorries left in the delivered modules: none. Split-off
unproved statements: 0. Existing stated dependencies are used as permitted by
stage 3; this report does not assert that their transitive proof closure is
axiom-free or that all project targets are finished.

## No longer needed

No original public import was removed. Removed the unused draft proof import
`Sheaf.Paper.CompletedKoszulReductionRoosTriangle`; replaced the draft import
`Sheaf.Paper.ConstantDirectImagePreservesComplete` by the actual dependencies
`Sheaf.Paper.LocalCompletenessModels` and
`Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`. Removed an unused draft
private helper for scalar differences on relative complexes.

The item's old proof plan no longer needs sequential evaluation fullness
(`lem-weil-pbc-sequential-tower-evaluation-full`): a levelwise isomorphism conjugates
`1-T` on the two products, and derived-limit uniqueness compares the vertices.
There is no strict-tower lift to choose. It also does not require the higher-level
`prop-weil-pbc-koszul-reconstruction`: the unit-compatible Koszul/quotient comparison
and the canonical completion Roos triangle suffice.

The flatness argument uses algebraic inverse image and descent of tensor kernels,
so the old applications of `lem-pc-bounded-above-flat-kflat-site` and the K-flat
preservation theorem `lem-weil-pbc-ringed-pullback-preserves-kflat` are unnecessary. It needs no DVR
calculation (`lem-weil-l-adic-extension-integers-dvr`) or two-term finite-free
resolution from `lem-weil-pbc-completed-constant-sheaf-reduction` to compare the two
flatness conditions. The `KFlatRingedToposPullback` module remains imported for its proved private
`inverseImageOfUniverses` adapter; its K-flat preservation theorem is not applied.
The module's node is therefore retained as a dependency for that adapter.
The sequential-evaluation-fullness and Koszul-reconstruction entries were removed
from `tool_uses`; the other approvals were preserved in their original order.
These are removals from this proof's planned route, not claims that the declarations
are unused throughout the library. No Lean module or declaration was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old plan introduced a strict-tower morphism lifting theorem unnecessarily.
Compatibility of the supplied identifications already gives an isomorphism of the
sequences whose Roos triangles are needed. The existing derived-limit uniqueness
theorem compares their vertices directly. The existing item docstring retains the
old route as required; the node and the new reconstruction docstring describe the
actual proof.

The actual inverse-image completed coefficient ring must be retained in every
comparison. The proof constructs its isomorphism with the completed ring on the
covering scheme, proves projection compatibility, and transports the quotient
adjunctions and transitions. It does not replace that ring by a constant ring by
definitional equality. It imposes no Noetherian hypothesis on the covering scheme.
Empty schemes, zero objects, and zero or unit ideals introduce no cancellation by
a nonzero element. The tensor descent argument also applies to empty strata.

## New nodes

`lem-weil-pbc-supplied-model-reconstruction`, in
`dag/nodes/sec-smooth-base-change/lem-weil-pbc-supplied-model-reconstruction.json`,
is the fully proved reconstruction lemma used by the forward implication. Its
statement, source, proof steps, Lean attachment, LeanSearch, LeanFinder/Loogle and
source-grep searches, and blueprint ancestry are recorded. Blueprint searches for "supplied model" and
"compatible reductions" found no existing statement of this reconstruction
(the latter finds the canonical levelwise-truncations node). No definition or
statement change record is needed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
