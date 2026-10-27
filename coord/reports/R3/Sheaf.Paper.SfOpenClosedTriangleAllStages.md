## What changed

The integral/rational hole is reduced to the geometric operation-realization lemma.
All five delivery modules compile together through `lcompile.py --all`
(result `fbf361d42793b6bfbcbb8fe9`, exit code 0), without errors or warnings.
All five original stage-theorem signatures are unchanged; the finite proof and
the other three original holed declarations are unchanged.
The combination proof is written: the actual completed sheaf kernel sequence is
short exact; exact localization gives its distinguished triangle with the specified
maps; the closed reflective adjunction gives cross-object orthogonality in every
shift; restriction gives the integral triangle; raw tensor localization gives the
rational functors, maps, triangles and orthogonality. Triangle-morphism extension
proves uniqueness and naturality for every middle map at both stages.

`SfOpenClosedTriangleData` extracts the original presentation data and proved sheaf
API, retaining their names, signatures and bodies and reexporting them publicly
from the item module. It adds proved closed-adjunction, closed-image exactness and
short-exact-sequence lemmas. `SfExactLocalizationTriangle` and
`SfRecollementRestriction` contain the general proved constructions. The extraction
avoids a circular import from the geometric lemma; no source-library file changes.
The change record is
`coord/changes/sf-recollement-presentation-data-extraction.md`.

## Proved and sorry left

Original holes: four. Closed by decomposition: one,
`WeilConjectures.sfOpenClosedTriangle_integral_rational`.
New holes: one,
`WeilConjectures.sfIntegralKernel_operation_realization`
(node `lem-sf-integral-kernel-operation-realization`).
This is a decomposition, not a net hole reduction. Additivity is proved by the
restriction instances, not assumed in the new lemma.
The new statement contains
constructibility, the recorded operation vertices and canonical coefficient
linearity; it assumes or concludes no triangle, orthogonality, uniqueness,
naturality or rational passage. All these other parts are proved in the item.

The three original remaining holes are
`WeilConjectures.sfOpenClosedTriangle_qbar`,
`WeilConjectures.sfOpenClosedTriangle_rational_weil`, and
`WeilConjectures.sfOpenClosedTriangle_qbar_weil`, all attached to
`prop-sf-open-closed-triangle-all-stages`. Their original statements and proof
docstrings are retained. The finite theorem and all previously proved declarations
are preserved. There are no holes in definitions or private helpers.

New completed proofs: `sfRecollementModule_closed_adjunction`,
`sfRecollementModuleDirect_exact`, `sfRecollementModule_shortExact`,
`sfExactLocalizationPresentation_counit`, `sfExactLocalizationPresentation_unit`,
`sfExactLocalizationPresentation_distinguished`,
`sfExactLocalizationKernel_orthogonality`,
`sfRecollementRestriction_distinguished`, and
`sfRecollementRestriction_orthogonality`, with explicit rational tensor-induction
and triangle uniqueness/naturality helpers in the item module.

## No longer needed

The integral orthogonality argument uses closed reflection and the unit kernel;
it requires no separately constructed open adjunction or open/closed disjoint-support
comparison. The derived short exact sequence is Mathlib's
`DerivedCategory.triangleOfSES_distinguished`, and the exact derived adjunction is
`Sheaf.CategoryTheory.ExactDerivedAdjunction`; the stronger monoidal/K-flat derived
adjunction interface is unnecessary for this categorical step.

The rational passage uses the existing raw scalar localization directly, so
`lem-sf-rational-localization-triangle-orthogonality` and
`Sheaf.Paper.SfRationalLocalizationOrthogonality` are not needed for the now-written
integral/rational argument. They are not withdrawn: other unfinished arguments
may use them. The common-stage dependency is retained for the original qbar hole.
The geometric realization dependencies remain needed beneath the new geometric
lemma; none is claimed pruned merely because its parent was reorganized.
No module is withdrawn and no adopted-source declaration is removed.

All former direct proof dependencies displaced by the reorganization are accounted
for as follows. The new geometric node retains
`lem-sf-immersion-completed-pullback-comparison`,
`lem-sf-integral-open-reduction-comparison`,
`lem-sf-open-reduction-adjunction-transport`,
`def-weil-integral-rational-qbar-compact-support`,
`lem-sf-ringed-open-roos-preservation`, `lem-sf-open-semilinear-tensor-model`,
`lem-sf-open-quotient-koszul-completeness`, `prop-weil-pbc-direct-image-limits`,
and `lem-sf-finite-immersion-constructibility-interval`.
`lem-weil-integral-constructible-triangulated` remains a dependency of the
restriction construction. `def-weil-derived-direct-image` and
`def-weil-derived-complete-integral-detailed` remain statement dependencies.
`lem-weil-pbc-complex-ses-triangle` is replaced by Mathlib's derived short-exact
triangle. `lem-sc-derived-adjunction-from-underived` is replaced by the exact
(non-monoidal) derived adjunction. `lem-kun-dimension-finite-type` is unnecessary
for the now-written categorical argument; the geometric node instead retains
the finite-immersion constructibility and completed direct-image interfaces.
Together with the rational-orthogonality package named above, these are all
removed direct proof-dependency edges; they are not module withdrawals.

Removed private proof imports from the item:
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`,
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
`Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`, and
`Sheaf.Paper.QcqsCompactSupportRealization`. The four ringed modules belong only to
the extracted sheaf API, not the stage assembly. The compact-support realization is
needed only in the geometric comparison. The original public imports are reexported
through the data module, with redundant direct imports removed from the item.
The new data module does not import the finite-kernel assembly, finite local
constancy, finite open interval, triangle-morphism extension, integral triangulation
or compact-support realization: those proofs are outside its role.

## Where the brief, the DAG or earlier work was wrong

The supplied rational localization and qbar common-stage packages quantify over a
finite-field datum and require schemes over its algebraic closure. This item's
integral/rational and qbar theorems allow an arbitrary base field. Thus those
packages cannot be directly applied to those clauses. Raw rational localization
avoids that mismatch in the completed integral/rational assembly. The remaining
geometric comparison is stated for exactly the arbitrary-field hypotheses of the
item; no characteristic hypothesis or finite-field descent assumption is added.

The geometric interfaces also use distinct presentations: immersion completed
pullback is normalized on the PBC completed model, open reduction is stated on
its slice-site operations, and the item fixes the kernel of the actual sheaf
unit. Connecting those concrete presentations, their coefficient maps and their
recorded operation values is the separate geometric result left in the new node.
The categorical proofs do not assume those presentations are definitionally equal.

Edge cases checked in the general arguments: zero objects, empty complements,
arbitrary unbounded representative complexes, negative as well as positive shifts,
and arbitrary rational morphisms (tensor induction, without an integral lattice).
The unit's sheaf short-exact-sequence route is retained; no unit step is bypassed.
The import overlay is acyclic. A DAG traversal found an existing cycle between
`lem-pc-ring-hom-extension-differential` and its adjacent-case dependency;
checking every newly added edge found no cycle introduced by this packet.

## New nodes

`def-sf-recollement-presentation-data` records the extracted unchanged data and
proved sheaf API in `SfOpenClosedTriangleData`.

`lem-sf-exact-localization-triangle` records the localized actual maps, derived
short-exact triangle and reflective-kernel orthogonality in
`SfExactLocalizationTriangle`. All declarations are proved.

`lem-sf-recollement-full-subcategory-restriction` records the actual full-subcategory
restriction, scalar/additive instances, triangle and orthogonality transport in
`SfRecollementRestriction`. All declarations are proved.

`lem-sf-integral-kernel-operation-realization` records the strictly geometric part
of the integral argument in `SfIntegralKernelRealization`. Its proof docstring
contains the source and complete mathematical argument. Its only hole is the
named public theorem. The original node's route and attachments are updated to
match this decomposition. Blueprint searches for kernel localization, exact
localization, and triangulated subcategories found related definitions and
coefficient-change results but no duplicate of these four statements.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
