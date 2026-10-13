## What changed

Closed the proof body of `exists_moduleCohomology_ext_edge_comparison` without
changing its statement or existing public imports. It now selects two explicitly
constructed `moduleCohomologyExtResolutionEquiv` families and combines their
coefficient naturality with the normalized edge identity.

Added `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`, which
constructs the equivalence using standard module and abelian injective resolutions,
Hom-complex cohomology, the sheafification/free-abelian/Yoneda section adjunction,
acyclic-resolution comparison and the free-abelian-terminal/constant-integer
isomorphism. All definition data is implemented in Lean. It chooses no natural
comparison from a mere existence assertion. The concrete Ext and section helpers
adapt the private constructions in `ExtRightDerivedHom` and
`CohomologyRightDerivedSections`; their existing existential interfaces cannot
specify the normalization needed here.

Added `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge`, isolating the
edge calculation for this fixed construction. Both new results are strictly parts
of the argument: one is coefficient naturality for a constructed equivalence on
one scheme; the other is one cross-scheme equality for that same construction.
Neither asserts the original coherent existence statement.

Updated the item's node to record this implementation. No existing interface,
target, definition, unit realization or other group's module changed.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.Scheme.Modules.exists_moduleCohomology_ext_edge_comparison`
(node `new-module-cohomology-ext-edge-comparison`). Its assembly proof compiles
from the normalized coefficient and edge statements.

New holes (decomposition, not a completed axiom-free proof):

- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv_naturality`
  (node `new-module-cohomology-ext-resolution-naturality`).
- `AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv_edge`
  (node `new-module-cohomology-ext-resolution-edge`).

The constructed `moduleCohomologyExtResolutionEquiv` and all its construction
helpers have complete proofs/bodies. The generic Ext/Hom-complex naturality
and `ExtEdgeResolution.siteSectionsNatIso` are fully proved; the latter is
used directly in the equivalence construction. No definition contains sorry. There are no
sorries in the original module. Local hole accounting: one closed, two added; this is a
decomposition, not an independent proof of the target. Closure-wide progress
is determined by the pinned sorry ledger and includes imported dependencies.

Coefficient naturality was attempted using resolution-forgetting naturality
and `acyclicComparison_naturality`. The Ext/derived-sections natural isomorphism
is proved and retained. The module-comparison assembly still exceeded the
single-file time limit; its exact remaining square is a named theorem with
a complete mathematical proof. Unused local assembly helpers and their
proof-only `AcyclicComparisonNatural` import were removed.

## No longer needed

The unused proof-attempt import
`Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural` was removed
from the new construction module; its generic tool remains in the lower proof
plan, and can be imported when that theorem is proved.

No original public import was removed: both specify types in the unchanged
statement. The construction module imports the narrower source cohomology
definitions; scalar/base-change comparison definitions are imported by the
edge module where its statement needs them. The original plan's following existential-comparison/interface nodes
and modules are not needed by this implementation, and are not imported:

- `lem-sc-module-cohomology-source-comparison` /
  `Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`.
- `lem-sc-site-cohomology-right-derived-sections` /
  `Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections`.
- `lem-weil-pbc-module-cohomology-fmap-functorial` /
  `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`.

This is pruning from this item's proof, not a claim that no other target uses them.
The two actual type-defining dependencies remain as statement dependencies.
Forgotten-injective acyclicity and Mathlib's resolution and homology machinery
remain necessary in the constructed comparison and the lower proof plans.

## Where the brief, the DAG or earlier work was wrong

The previous attempt quantified over arbitrary independently chosen natural
additive equivalences. Naturality in coefficients does not normalize those
choices across schemes: modifying just one family by negation already obstructs
an edge equality in degree zero when its edge map has a non-2-torsion image.
The delivered edge theorem quantifies only over schemes, morphisms, modules,
degrees and elements, and names the concrete resolution equivalence.

The source-comparison existential theorem cannot establish this particular
normalization. The implementation reproduces the concrete private resolution
and section constructions rather than selecting an arbitrary witness of it.
No source statement or target was weakened. The unit `sk-thm-p1` and all its
`realized` entries are preserved.

Read the original node, all eight planned dependencies and their Lean
interfaces, the unit record, and Stacks 03FD, 01FB, 01F7 and 06XR online.
The LeanSearch service was unavailable; LeanFinder, Loogle and source grep ran,
and their actual outcomes are recorded in both new nodes.

Edge checks: in degree zero the construction is evaluation at the terminal
generator/1 and the edge is canonical restriction; zero coefficients and empty
schemes give zero groups; the identity scheme map gives the identity cohomology
map. Neither flatness nor acyclicity of the direct image is added.

The generic acyclic-comparison naturality node belongs to another unit; it is a
tool about resolutions, not a replacement for the unit route. The maintainer can
record that tool use if the route checker requires it.

## New nodes

`new-module-cohomology-ext-resolution-naturality`: the coefficient-naturality
square for the explicitly implemented resolution comparison, in
`lean/Sheaf/AlgebraicGeometry/ModuleCohomologyExtResolutionNaturality.lean`.
Its statement records the precise normalization, its source and proof explain
the common section complex, and its data construction is fully implemented.

`new-module-cohomology-ext-resolution-edge`: the identity direct-image edge
calculation for that same comparison, in
`lean/Sheaf/AlgebraicGeometry/ModuleCohomologyExtResolutionEdge.lean`.
It excludes arbitrary comparison families and follows the Stacks 01FB diagram.

No change record is needed: no existing interface changed and no forced
adaptations were made.

## Second reading by S2

1. Compared the delivered target module with the repository version. The target statement and existing declaration signatures are unchanged; the only added import is the proof-side resolution edge module used by the proof.
2. Compiled the delivered modules with `lcompile.py`. The target compiles with the two documented split-off theorem holes; no definitions contain `sorry`, and no forbidden declarations were found.
3. Checked the split-off statements and nodes. `moduleCohomologyExtResolutionEquiv_naturality` and `moduleCohomologyExtResolutionEquiv_edge` are strictly smaller than the target, have source/proof documentation, and are recorded as split nodes. Search records show no existing exact declaration.
4. Read the proof top-down. The target is assembled directly from the concrete normalized equivalence and the two split lemmas. The proof-only resolution machinery remains in the construction module because it is required to elaborate the concrete definitions; no shorter existing theorem was found. The unused acyclic-comparison-natural import and planned existential comparison dependencies are pruned as recorded above.
5. Checked node/Lean agreement. The target node records the two proof dependencies and the construction and edge nodes record their corresponding declarations, statements, origins, searches, and split status. No unit realization was changed.

I changed only this report and restored the construction module's required public imports after checking that making them private breaks compilation of the concrete exposed declarations. No Lean proof or statement was otherwise changed during second reading.
