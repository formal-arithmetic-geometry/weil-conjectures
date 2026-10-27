## What changed

The original `condensedTateIntegralTower` proof now assembles the geometric finite-smooth
system, the strict normalized tensor and unit models, constructible-complete uniform
reconstruction, and the finite exceptional coefficient square. Its statement and the
`ReconstructionResult` predicate are unchanged. The universal quantification over the
supplied finite levels and reduction data is retained.

`AlgebraicGeometry.Scheme.singleDegreeUniformReconstruction` is proved from the
existing uniform reconstruction declaration and the proved constructible-completeness
helpers. The proof uses actual projection counits, transports constructible cohomology
to actual reductions, supplies intrinsic completeness in the required presentation,
and obtains compatible etale origins through the existing complete-category theorem.

The existing definitions and proved coefficient lemmas through `IdentifiesExceptional`
move, with their original names and signatures, to the publicly reexported
`CondensedTateIntegralTowerData` module. This permits the two strictly lower coherence/model
lemmas to use the data while the original theorem imports those lemmas, without an import
cycle. Local irreducibility settings reduce unnecessary elaborator unfolding. No adopted
source-library module is changed.

Validation: the assembly compiled cleanly through `lcompile.py` (21.4 seconds),
against the four compiled sandbox dependencies. The two concentration helpers also
compiled in their scratch check (24.3 seconds); the combined shortened interface is
being checked by the required delivery process.

The private helpers `finite_concentrated` and `level_concentrated` prove the two
concentration assertions from the explicit single-complex models and Mathlib t-structure
vanishing. Those assertions are removed from the residual normalized-tower theorem.

The private assembly lemmas prove invertibility of gamma at the unit, paste the finite
gamma square with the actual reconstruction square, transport fixed-coefficient
constructibility across isomorphisms, and specialize general single-degree reconstruction.

## Proved and sorry left

The original module had one hole,
`AlgebraicGeometry.Scheme.PurityIntegralTower.condensedTateIntegralTower`.
Its body now contains a complete assembly proof from two genuine lower statements.
This is a decomposition, not an unconditional proof: one original hole is closed and two
lower holes are added. The data module and single-degree reconstruction module have zero
holes. Existing library dependencies may themselves have holes; none is copied or added
by this delivery.

The new theorem `AlgebraicGeometry.Scheme.singleDegreeUniformReconstruction` is proved
from the existing reconstruction API and has no hole of its own. All extracted
coefficient lemmas keep their existing complete proofs.

The two residual named theorems are:

- `AlgebraicGeometry.Scheme.PurityIntegralTower.normalizedTateTensorTower`
  (`lem-pur-normalized-tate-tensor-tower`): only the actual strict root-tensor model,
  projection normalization, all-pair coefficient squares and common local models. It
  assumes no field or smooth morphism and asserts no derived-limit reconstruction or
  exceptional comparison. This is source Steps 2--5, independent of Steps 6--8.
- `AlgebraicGeometry.Scheme.PurityIntegralTower.finitePuritySourceUnitReduction`
  (`lem-pur-finite-source-unit-reduction`): the equality of the specified scalar/site,
  source-unit and root-tensor balancing maps, independent of all smooth orientations,
  completeness and reconstruction. This is the source-edge coherence used in Step 8.

Both have source references, complete proofs in words, their own modules and DAG nodes.
The existing root-local-model theorem provides ordinary completed-root reductions, but
not the retained evaluation-normalized d-fold strict tower in this coefficient
presentation. The existing finite-Tate scalar-source normalization theorem uses a fixed
annihilator and a different ordinary-line presentation; no unchecked replacement of its
maps by the present maps is used. The root-model and source-unit statements remain to be
proved.

## No longer needed

No existing module is withdrawn, and no adopted source declaration is removed. The
original public imports remain public through the extracted data module. There is no
whole-module pruning in this packet.

The parent proof no longer directly uses Noether normalization or its dimension bound:
the existing finite-smooth theorem supplies Noetherianity and compactification, and the
actual complete-category interface requires finite type rather than an extra dimension
hypothesis. Thus `lem-zl-noether-normalization-field` and
`lem-zl-noether-normalization-dimension` are removed from this node's direct proof route.
The same applies to a separate direct call of `lem-weil-pbc-finite-type-over-noetherian`
and `def-weil-finite-type-morphism`; their geometric consequences come from the finite
smooth system and Mathlib composition lemmas.

The root tensor, K-flat reduction, compatible-generator, strict-tower and adic-lisse
steps remain needed in the new root-model node. Uniform reconstruction and compatible
origin arguments remain needed in the proved single-degree reconstruction node. They
are relocated dependencies, not claimed pruned mathematics. All earlier coefficient
proof dependencies remain attached to the data node.


The parent's removed direct tool approvals are
`lem-weil-pbc-finite-type-over-noetherian`, `lem-zl-noether-normalization-field`,
`lem-zl-noether-normalization-dimension`, `lem-pur-site-restriction-module-adjunction-exact`,
`lem-pur-derived-change-of-rings`, `lem-weil-pbc-reconstruction-uniform-tower`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`lem-weil-pbc-finite-ring-constructible-derived-origin`,
`lem-weil-pbc-normalized-etale-origin-witnesses`, `det-def-sp-tate-twist-locally-free`, and
`lem-weil-pbc-constant-completion-equivalence`. Apart from the dimension argument noted
above, these mathematical dependencies are retained in the lower argument. This packet
requests no new maintainer tool approval.

## Where the brief, the DAG or earlier work was wrong

The eight-step mathematical plan remains the route. Its last step implicitly identifies
lambda at the coefficient unit with root reduction. This requires an equality of the
specified maps, recorded as the independent source-unit coherence theorem, not an
arbitrary choice of an isomorphism. Likewise the common local model must retain the
actual root projection and its evaluation square; arbitrary local freeness alone does
not imply `ProjectionNormalized`. The new model theorem states this normalization
explicitly, including the empty tensor and equal-level cases.

Edge cases checked in the formulations: empty schemes, tensor power zero, equal quotient
indices, arbitrary positive-characteristic base fields, and ell=2. No target signature,
coefficient construction, orientation or normalization is weakened.

## New nodes

`def-pur-condensed-tate-integral-tower-data` attaches the unchanged extracted data and
previously proved coefficient declarations. Its statements and constructions preserve
the original mathematical interface.

`lem-pur-single-degree-uniform-reconstruction` attaches the proved general reconstruction
lemma. It combines existing reconstruction, intrinsic completeness presentation, and
constructible reduction control with equal model bounds.

`lem-pur-normalized-tate-tensor-tower` records source Steps 2--5 as a separate local-model
result about the actual integral line, independent of any reconstruction or purity map.

`lem-pur-finite-source-unit-reduction` records the source-unit balancing coherence from
Step 8 as a separate finite-coefficient result independent of purity orientation.

Change record: `coord/changes/R1-condensed-tate-data-extraction.md`.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
