## What changed

Proved `AlgebraicGeometry.openComparison_ordinary_structure_class` in
`Sheaf.AlgebraicGeometry.OpenSectionsOrdinaryStructureClass` without changing its
signature, definitions, visibility, or imports. Added fully proved private helpers
for normalization of homology by single-complex isomorphisms, compatibility with
exact scalar forgetting, and the ordinary section calculation.

The extension comparison agrees with homology of `extendSingleIso`, by naturality
of homologyπ and the extension/cycle comparison identities. Normalize source and
target homology by their single-complex comparisons. Naturality of the
scalar-forgetting homology isomorphisms reduces the ordinary comparison to its
zeroth component. The remaining section equation follows from naturality of
`openComparisonSectionsIso`, `StructureSheaf.const_one`, and
`tilde.toOpen_map_app`. The degree-zero single and over-unit maps are identities.
The proof works for every open, including the empty open, and the zero ring;
it does not assume affine U, quasi-coherence, or a derived equivalence.

Updated the existing node's proof narrative to record this realized route. All
private helpers are proved; no new modules or nodes were introduced.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.openComparison_ordinary_structure_class`
(node `lem-sc-open-sections-ordinary-structure-class`).

Holes added: none. Sorries left in the delivered module: none.
This is a proof, not a decomposition into new obligations.

## No longer needed

No imports removed and no dependency nodes or modules pruned. The existing public
imports supply the functors, ordinary comparison definitions, and extension
homology comparisons used in the unchanged statement and proof. The proof does
not use `exists_openComparison_cohomology_model_iso` or any derived comparison,
but its module remains needed for `openComparisonOrdinaryIso` and
`openComparisonSectionsIso`.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was needed. The DAG's ordinary
normalization route is implemented directly using Mathlib's existing
single-complex, cycle, and scalar-forgetting naturality identities. The referenced
unit has no realized statement or proof step at this node, and no unit route was
bypassed.

## Second reading by J1

1. Compared the delivered module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof text and private helpers were added. The DAG node changes only proof metadata and origin.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The private helpers and target use only the permitted library axioms.
3. Checked the proof route and helper statements. Each helper is a strict intermediate normalization or section calculation needed by the target, and no split-off theorem or new node was introduced. The route uses existing Mathlib and library identities and handles empty opens and zero rings.
4. Checked pruning and imports. All three public imports are used by the target signature or proof, so none can be removed. No proof dependency node or module is pruned; the route retains the unit's ordinary comparison path.
5. Checked the DAG against the Lean proof. The node's proof steps, dependencies, origin, and realized route describe the implemented normalization, scalar-forgetting, and section-naturality argument. No statement or definition was changed.

Changed in this second reading: added this review record only; no Lean code or signatures required repair.
