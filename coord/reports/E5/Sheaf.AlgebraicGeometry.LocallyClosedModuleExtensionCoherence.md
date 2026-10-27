## What changed

Constructed a fixed closed-then-open extension in
`Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionModel`. The geometric factorization,
coefficient identification, open extension and closed direct image use proved existing
constructions. Exactness, additivity, full faithfulness, and the specified restriction
isomorphism are proved. The model's functor and restriction definitions are irreducible;
callers use the named instances rather than unfolding the construction. A presentation
record has a proved equality to the explicit composite; its nonemptiness proof is the
explicit composite and reflexivity. Thus the presentation determines the data exactly
and lets the kernel keep the sheaf object construction abstract. `modelExtension_eq`
recovers the construction, and restriction is transported along this proved equality.

The item now assembles the system. Its Lean proof proves uniqueness of each normalized
objectwise binary comparison from full faithfulness and the restriction Hom bijection,
proves naturality from the two restriction naturality equations, constructs gamma as a
natural isomorphism, proves its normalization, and fills the original structure fields.
The original theorem signature is unchanged. Existing normalization proof-field types now
use transparent predicates expanding to definitionally identical equations; all existing
data definitions and the mathematical interface are preserved.
The coefficient parameter block is moved verbatim to a data module and publicly
reexported, to avoid a cycle with the new comparison statements.

The interface extraction, consumers, and new model instances are recorded in
`coord/changes/E5-locally-closed-module-extension-model.md`. No consumer source or
WeilConjectures source module is edited.

Validation: all six delivered modules compile cleanly through `lcompile.py --all` at
the ordinary 60-second limit: data 8.3 s, model 11.2 s, binary 7.7 s, boundary 7.9 s,
unit/associativity 8.0 s, and the item 12.0 s. The three unchanged direct consumers
also compile against the delivery: `LocallyClosedExtensionCoherence` (31.3 s),
`ContinuousQbarNormalizedSheafFiltration` (4.8 s), and
`NormAlgclOrderedFiniteModelFiltration` (8.9 s). Their temporary sandbox copies are
removed; no consumer edits are delivered. Profiling and diagnostic limits are removed.

## Proved and sorry left

This is a decomposition, not a net hole reduction. The item's single direct hole in
`AlgebraicGeometry.Scheme.locallyClosedModuleExtensionCoherence` is replaced by a complete
assembly proof from three strictly smaller obligations. The item itself has zero sorry.

Three holes are added, each the whole proof of one public theorem in its own module:

- `AlgebraicGeometry.Scheme.locallyClosedModel_boundary`
  (`lem-sfb-locally-closed-module-extension-boundary`): the normalized open and closed
  special cases of one fixed extension, without composition or coherence.
- `AlgebraicGeometry.Scheme.locallyClosedModel_binary_exists`
  (`lem-sfb-locally-closed-module-extension-binary`): an isomorphism on one module for one
  pair of immersions, with its restriction equation. Neither uniqueness nor naturality
  is assumed; both are proved in the item.
- `AlgebraicGeometry.Scheme.locallyClosedModel_unit_associativity`
  (`lem-sfb-locally-closed-module-extension-unit-associativity`): the formal identity and
  associativity laws for any supplied normalized natural binary comparisons on the fixed
  model. It constructs no binary geometric comparisons or boundary normalizations.

The two definition modules have no sorry. The model's exactness, full faithfulness and
restriction construction use no newly added holes. The private categorical lemmas in the
item, including restriction injectivity, binary uniqueness and normalized naturality,
are fully proved. The concrete proved API includes `factorization_nonempty`,
`open_extension_exists`, `modelExtension_additive`, `modelExtension_finiteLimits`,
`modelExtension_finiteColimits`, `modelExtension_full`, and `modelExtension_faithful`
in `LocallyClosedCoefficientImmersion`, together with its constructed `modelRestriction`.
The shared normalization predicates and the explicit
`LocallyClosedCompositeRestrictionMap` keep routine conversions over abstract functors.
The composite restriction is constructed componentwise over arbitrary categories and
instantiated at the model. Its component formula is definitional, avoiding nested
whiskering identities over concrete sheaf constructions. Choices in exposed data
definitions use proved existence theorems;
a binary comparison from an unfinished geometric statement is selected only after
its uniqueness has been proved in Lean. The boundary adjunction and closed comparison
are characterized by their specified unit/counit normalization, and the identity
comparison by its unit laws. Those witnesses are used inside the final theorem proof;
the extension functor itself is the fully constructed model.

## No longer needed

`lem-sfb-proetale-locally-closed-extension` and its module
`Sheaf.AlgebraicGeometry.ProEtaleLocallyClosedExtension` are no longer used on this branch.
Its existential interface does not retain the chosen factorization and normalized factor
maps needed for the remaining comparisons. The fixed model constructs those maps directly
from `proEtaleIdentifiedOpenClosed`, so the pointwise existential theorem is redundant here.
No module is withdrawn.

The following direct proof imports are removed from the item:
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`,
`Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`,
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`,
`WeilConjectures.CategoryTheory.SiteMorphismComposition`,
`Mathlib.CategoryTheory.Sites.CoverLifting`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit`,
`Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed`,
`Sheaf.AlgebraicGeometry.ProEtaleIdentifiedSupportedReconstruction`,
`Sheaf.AlgebraicGeometry.ProEtaleLocallyClosedExtension`, and
`Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage`.
The needed geometric results remain in the new obligations' proof dependencies; they are
not claimed mathematically obsolete. The model imports identified open/closed privately.
`lem-exc-proetale-closed-essential-image` remains needed transitively through identified
open/closed and supported reconstruction; only its redundant direct import is removed.
All original public imports of the item remain. The data module needs only Noetherian
schemes and StrictTowerOperations publicly.

## Where the brief, the DAG or earlier work was wrong

The existing pointwise extension theorem proves exactness and full faithfulness but its
existential conclusion alone does not identify the chosen support image or restriction
normalization with arbitrary other factorizations. It therefore cannot directly fill the
open/closed and composition fields. The fixed model retains the actual construction so
those remaining steps are explicit, separate obligations. The new nodes keep the original
intersection/shrinking, supported reconstruction and normalized-restriction proof route.
The unit record has no realized nodes for this assertion, and no unit route is bypassed.

Edge cases checked mathematically: empty source, zero module, identity arrows, clopen
arrows (both boundary clauses), and arbitrary identified coefficient presentations. The
open quasi-compactness hypotheses are supplied by the Noetherian ambient spaces.
The boundary assertion does not claim a shriek adjunction for a general immersion.

## New nodes

`def-sfb-locally-closed-module-extension-data` attaches the unchanged coefficient bundles
and coefficient-immersion operations to their extracted module. It also names the four
normalization formulas and their explicit composite restriction map over abstract categories,
without adding a mathematical assumption
or changing their interpretation.

`def-sfb-locally-closed-module-extension-model` records the concrete fixed factorization,
open extension and composite, with proved additivity, exactness, full faithfulness and
restriction comparison.

`lem-sfb-locally-closed-module-extension-boundary` is the open/closed special-case
comparison of this fixed model (original Steps 3--6).

`lem-sfb-locally-closed-module-extension-binary` is objectwise binary comparison existence
(original Steps 3--8); uniqueness and naturality are implemented by the parent.

`lem-sfb-locally-closed-module-extension-unit-associativity` is original Step 9, isolated
from the geometric comparison-existence arguments.

The existing node's proof, proof dependencies, proof origin and Lean attachment follow
this assembly. The change record is
`coord/changes/E5-locally-closed-module-extension-model.md`.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
