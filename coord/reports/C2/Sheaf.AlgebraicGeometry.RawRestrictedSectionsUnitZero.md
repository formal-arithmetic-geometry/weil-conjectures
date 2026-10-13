## What changed

Repair of the import_prune_check return: removed all four duplicated private declarations
`unit_plus`, `plus_unit_resolution`, `unit_homology_resolution`, and `augmentation_homology`.
The proof now imports and uses the existing public proved theorem
`CategoryTheory.Functor.rightDerivedPlusSingleUnitHomology_comp_comparison` from
`Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison`. Its normalization is
transported to the unbounded unit by the proved private helper `unit_zero_comparison`.
The other proved private helper `restricted_unit_zero` performs the exact-restriction
transport and single-complex cancellation. No Picard declaration is copied or imported.

`sectionsUnit` and the signature and visibility of `sectionsUnit_zero` are unchanged.
Restored the original module and public theorem docstrings. Updated the node's proof,
proof_deps and proof_origin to describe the public-theorem route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.RawRestrictedComparison.sectionsUnit_zero`
(node `lem-sbc-raw-restricted-sections-unit-zero`). No holes added or split off.
No sorry remains in the delivered module. Both private helpers are proved.
The imported bounded-below normalization theorem is already proved in the library.

## No longer needed

Removed the original proof-only import
`Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap`: its definitions are
already supplied through the retained public import
`Sheaf.AlgebraicGeometry.RawRestrictedHomotopySectionsIso`. Its node
`def-sbc-raw-restricted-cohomology-comparison-map` is still needed.

Removed the previous delivery's explicit proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`:
its declarations are already available through the retained imports.
The public normalization module
`Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison` and its node
`lem-sbc-right-derived-single-unit-homology-comparison` are now used and retained.
No other planned node or module is pruned. The Picard module
`Sheaf.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit` is not required.
The unit's realized lists are empty; no realized unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated four private generic calculations from the Picard
module. Those private declarations cannot be accessed by an ordinary import. Instead
of changing another module's visibility, this repair uses the existing public proved
bounded-below normalization theorem and proves only the additional unbounded transport.
All four declarations named in the return are removed. The original DAG route through
that public normalization theorem is now implemented.

The transport and cancellation use identities of natural transformations, including
zero coefficients and empty etale objects. No K-injectivity hypothesis on A[0], new
existence witness, changed definition, new node, or forced adaptation is introduced.

## Second reading by C2

1. Interface: compared the entire delivered module with the repository version.
   The existing `sectionsUnit` definition (including its body), and the signature
   and visibility of `sectionsUnit_zero`, are byte-for-byte unchanged. No target,
   definition, hypothesis, or conclusion changes; no change record is needed.
2. Proof: the module compiles locally without errors or warnings. Read both
   private helpers from top to bottom: unit compatibility transports the existing
   bounded-below normalization; unit naturality along the restriction single
   comparison and homology naturality reduce the remainder to inverse
   cancellation. No sorry or prohibited declaration occurs. A scratch-copy
   axiom check covers both private helpers, the definition, the public theorem,
   and the reused normalization theorem: all depend only on `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
3. Splits and small cases: no statement or hole is split off; both new private
   helpers are proved. No arbitrary existence witness is chosen. Their equations
   remain valid for zero coefficients and empty etale objects: the argument uses
   naturality and isomorphism cancellation, and explicitly handles every nonzero
   complex degree by its zero target. An independent Loogle query for
   `homologyRightDerivedFunctorObjSingleFunctorIso` returned no hits; local
   searches for the unbounded comparison and single-unit normalization confirm
   that the existing public bounded-below theorem is reused. The canonical
   single-degree lemmas are bounded-below and do not replace this transport.
4. Route and pruning: the public homotopy-sections import is needed for
   `underivedSections` and `underivedSingleIso`. The normalization import is used
   only in a proof and is correctly non-public. The removed explicit comparison-map
   import is redundant through the retained public import, and its node stays
   in `proof_deps`. Every old proof dependency is still used, so no node or module
   is pruned from the target closure. Checked `sk-lem-failure-field.realized`: its
   statement and step lists are empty, and no realized unit route is bypassed.
5. DAG: parsed JSON comparison changes only `proof`, `proof_deps`, and
   `proof_origin`. Their three dependency IDs match the definitions and theorem
   actually used; the steps describe both helpers and the final specialization.
   No new node is added. Verdict: pass.

Second-reading changes: removed an accidental extra blank line in the existing
module docstring and restored literal Unicode JSON formatting. No proof changes
were needed. The original hole closed is
`AlgebraicGeometry.Etale.RawRestrictedComparison.sectionsUnit_zero`; zero holes
are added (one proved of one, no decomposition).
