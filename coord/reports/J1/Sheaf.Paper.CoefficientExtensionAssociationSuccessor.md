## What changed

Filled `WeilConjectures.coefficientExtensionAssociation_successor` without changing
its statement, docstring, or public imports. The proof compares the conjugated
successor with `integralScalarTransition` on local pure tensors, uses the proved
tensor Hom-ext API, and cancels the finite coordinate isomorphisms.

Added three fully proved helper modules under the namespace
`WeilConjectures.CoefficientExtensionAssociation`:

- `CoefficientExtensionAssociationQuotientUnits`: normalized quotient unit
  sections and their successor compatibility, obtained from the ordinary
  quotient's adjoint-mate characterization and `M.transition`.
- `CoefficientExtensionAssociationScalarUnits`: the evaluation unit equation
  identifies finite normalized scalar units with the system unit; its
  sequence-site naturality preserves compatible pairs of sections.
- `CoefficientExtensionAssociationTensorCoordinates`: computes inverse balanced
  coordinates on pure tensors and proves their reduced-coefficient successor
  formula by semilinearity.

The new definitions construct actual adjunction-unit sections and their images
under the supplied isomorphisms. The quotient adjunction witness is the existing
one whose sectionwise unit formula fixes the data used downstream. No arbitrary
existence witness or data with a missing proof is introduced.

Proof imports reuse the proved private section, abelian-sheaf conjugation, and
sheafified tensor Hom-ext lemmas in `CoefficientExtensionOrdinaryStrictTensor`,
and the proved unit normalization in `CoefficientExtensionFiniteAssociation`.
The good-complex existence theorem in the former module is not applied to an
arbitrary complex. No other existing module or its interface changes.

## Proved and sorry left

Closed the original one hole:
`WeilConjectures.coefficientExtensionAssociation_successor`
(node `stage3-pur-extension-association-successor`).

The three helper-node theorems are proved, not deferred obligations:
`quotientUnitSection_transition`, `evaluatedUnitSection_transition`, and
`associatedTensor_transition`, in the namespace above. All private helpers are
also proved. Added holes: zero. Remaining holes in the item and new modules: zero.
No axioms, unsafe declarations, or definitions with `sorry` are added.

All four packaged modules compiled with `lcompile.py --all`, without errors or
warnings. The final delivery preflight also checks the pruned proof imports,
declaration interfaces, axioms, hole counts, and per-file compilation limits.

## No longer needed

The planned dependencies `lem-pur-system-scalar-generators`
(`Sheaf.Paper.SystemScalarGenerators`) and `lem-pur-system-scalar-coherence`
(`Sheaf.Paper.SystemScalarCoherence`) are not used. Their `SystemScalarModel` API
is unnecessary for the supplied `SemilinearSections.ScalarData`: ordinary
adjunction units and the existing proved tensor Hom-ext helpers give the required
calculation directly. These two planned dependencies are removed from this
node's proof route; neither module is imported for this proof.

No original public import is removed. No library module is withdrawn, and no
upstream declaration is removed or changed. Other needed dependencies now occur
through the three proved helper nodes; their own dependency records retain them.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction is needed. The argument works at n = 0,
with zero sections or zero complex terms, with identity horizontal arrows in the
scalar-unit lemma, and without flatness, boundedness, or ramification conditions.
The blueprint unit's route is preserved.

The initial direct concrete calculation triggered expensive kernel unfolding of
restriction-of-scalars carriers and coefficient constructions. Native-carrier
section definitions and generic categorical unit/conjugation lemmas keep these
constructions abstract. The self-contained quotient, scalar-unit, and tensor
calculations are packaged separately after addressing those definitions. No
heartbeat or file-time limit is raised, and respectTransparency remains enabled.

## New nodes

`stage3-pur-extension-quotient-unit-successor` records the fully proved successor
formula for quotient unit sections. It is a strict unit-section calculation,
not the item's all-sections scalar association statement.

`stage3-pur-extension-scalar-unit-transition` records the fully proved naturality
of the normalized finite scalar unit on any compatible pair of system sections.
It does not assume or construct balanced association coordinates.

`stage3-pur-extension-associated-tensor-transition` records the fully proved
successor formula only on local pure tensors in balanced association coordinates.
The item supplies the separate tensor Hom-ext and conjugation argument extending
that formula to every section.

There are no change records: the delivery changes only the assigned module,
its proof-node record, and new modules and their nodes.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
