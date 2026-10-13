## What changed

Proved `TopCat.Sheaf.positive_refinement_factor` with its existing signature and
public imports unchanged. The proof explicitly glues zero and signed canonical
unit sections on the record's disjoint cover, constructs the component maps,
checks their composite unit images by sheaf separation, and assembles them by
`Sigma.desc` and `Sigma.hom_ext`.

Added two reusable proved theorems, each in its own module:
- `TopCat.Sheaf.abelianIntegerExtension_section_lift` in
  `Sheaf.Topology.AbelianIntegerExtensionSections`: an actual section-to-map
  construction, reusing the proved local-generator module's private naturality
  and counit helpers via a proof-only `import all`.
- `TopCat.Sheaf.abelianIntegerExtension_unit_injective` in
  `Sheaf.Topology.AbelianIntegerExtensionHomExt`: maps are determined by their
  unit image, using the existing proved integer-germ coordinates inside the open,
  zero source stalks outside it, and Mathlib section extensionality.

The item's two new imports and all new modules' proof dependencies are plain
imports. No existing definition, declaration signature, visibility, or target
statement changed. No change record or forced adaptation is needed.

## Proved and sorry left

Closed the original hole in `TopCat.Sheaf.positive_refinement_factor` (1 of 1
original holes in the item). Also proved both new helper declarations
`TopCat.Sheaf.abelianIntegerExtension_section_lift` and
`TopCat.Sheaf.abelianIntegerExtension_unit_injective`.

Holes added: none. Holes left in delivered modules: none. Split-off open statements:
none. This is a proof, not a decomposition: one existing hole closed and no lower
hole added. `#print axioms` for all three declarations reports exactly
`propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.

## No longer needed

No original import, proof dependency, or baseline module was pruned. The original
proof dependency `def-sc-abelian-open-extension-by-zero` remains used in the
canonical units and extensions. Added only the two proved helper nodes to the
factor node's proof dependencies.

Removed the earlier worker's new
`positive_refinement_factor_components` theorem and its undelivered component
node: its statement was just the original factorization expressed through the
coproduct universal property. This removal is not counted as baseline pruning.
Removed identical sandbox copies of `ConstantSubsheafPositiveRefinementData`
and its node; they were not changes to deliver. Removed redundant experimental
Mathlib imports for gluing and stalks; the unchanged public data import already
makes those Mathlib declarations available.

## Where the brief, the DAG or earlier work was wrong

The earlier component theorem was mathematically equivalent to the original
item and left the entire geometric argument open. Its report's claim that this
was a strictly smaller intermediate statement was incorrect. Replaced it with
the actual signed-cover argument, then closed both universal-property substeps.
A broader search by integer germ generation found the existing proved
`abelianOpenExtension_integer_germ_coordinates`, which supplies the shortest
available uniqueness argument. No source or statement discrepancy was found in
the original item. Stacks tags 00A5 and 0A38 were read to check the source route.

## New nodes

`lem-sc-abelian-integer-extension-sections` records the proved construction of a
map whose unit image is a specified section; it cites the local-generator
construction and its extension-section formulas.

`lem-sc-abelian-integer-extension-hom-ext` records proved injectivity of unit
image evaluation; it cites integer-germ coordinates and extension-by-zero stalks.
Both nodes have verbatim Lean statements, complete proofs, source citations,
all three required search kinds (LeanSearch unavailable; no conclusion drawn),
creation metadata, and the parent item's chapter and unit.

## Second reading by Q3

1. Compared delivered modules with the repository. PASS: the existing factor
   signature is byte-for-byte identical, its docstring is retained, and its only
   changes are its proof and two plain imports. The other two modules are new.
   There are no existing interface changes or altered definitions.
2. Compiled every delivered file through `lcompile.py --all`, with no errors or
   warnings. PASS: no delivered `sorry`, axiom, unsafe declaration, opaque
   declaration, extern or implemented_by; all constructions are real. Scratch
   `#print axioms` checks on all three theorems give only the three allowed axioms.
   No data is selected from an unproved existence theorem.
3. Reviewed both new helper statements and searched Mathlib, the upstream root,
   and Sheaf using unit-image, hom-ext and integer-germ terminology. PASS: both
   helpers are true, strictly part of the argument, reusable beyond the item,
   and now proved. Existence reuses existing construction helpers; uniqueness
   reuses integer germ coordinates rather than restating factorization. Checked
   empty U, the zero sheaf, m=0, n=0, absent refined pieces, and arbitrary signed
   coefficients: the proofs require no nonemptiness or sign-square assumption.
4. Reviewed the proof top downward and removed redundant imports. PASS: gluing
   and separation use proved Mathlib results, map construction uses proved
   library helpers, and uniqueness uses proved library stalk results. Every old
   proof dependency remains accounted for. The unit
   `dag/units/sk-thm-curveestimate.json` realizes only the upper cohomology target
   and no intermediate step here; its route is unchanged and no unit is bypassed.
5. Compared the nodes with the final Lean. PASS: the factor node records gluing,
   section lifting, unit-image injectivity, and coproduct assembly. The two new
   nodes record their actual proofs and imports, with proof_deps equal to the
   union of their proof-step uses. Existing statement and stmt_deps fields stay
   unchanged. No dangling reference to the removed component node remains.

Second reading changed: removed the equivalent component-hole restatement,
wrote the full gluing proof, added and proved the two genuine universal-property
helpers, removed unchanged sandbox copies and redundant imports, and rewrote the
proof records and report to describe the final implementation.
