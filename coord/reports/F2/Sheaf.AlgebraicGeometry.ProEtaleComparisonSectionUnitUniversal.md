## What changed

Proved `AlgebraicGeometry.proEtaleComparisonSectionUnit_bijective` in
`Sheaf.AlgebraicGeometry.ProEtaleComparisonSectionUnitUniversal`, preserving its
entire signature and the existing concrete unit definition.

Existence uses the inverse-image adjunction on each local étale site. The proof
constructs the local transpose, proves its compatibility with inverse-image
composition, and verifies both pro-étale naturality and the diagonal equation.
Uniqueness uses local representatives of the sheafified left Kan extension:
after an étale covering sieve, every decoded section is the restriction of a
diagonal section. Naturality and separatedness give equality of extensions.
All supporting helpers are private and fully proved in this module.

Added the proof-only import
`Sheaf.AlgebraicGeometry.EtaleInverseImageKanRepresentative`. Updated the theorem's
proof docstring and its DAG node's proof, proof dependencies, and proof origin.
No public definitions or statements were changed; no other modules were adapted.

Validation: the complete proof compiled cleanly through `lcompile.py` in 18.7 s.
An explicit `#print axioms` check reported exactly `propext`, `Classical.choice`,
and `Quot.sound`; the temporary check was removed afterward. Covering sieves
handle empty schemes and empty section sets without choosing any point or
arbitrary witness for a definition.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.proEtaleComparisonSectionUnit_bijective`
(node `lem-cbc-comparison-section-unit-universal`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the item, and no other
Lean module or split-off statement is added. This is a proof, not a decomposition.

## No longer needed

Removed the original proof-only import
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`.
The proof no longer needs its node
`lem-weil-pbc-sets-etale-inverse-image-restriction` or that node's downstream
proof plan. Its dependency was removed from the updated universal-property node.
This records pruning from this proof; other parents may still need the module.

Also removed the redundant direct proof-only import
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`. Its theorem is
still used and its node remains in `proof_deps`; the module is already publicly
imported by the retained `EtaleSetTerminalTransport` import. This removal does
not prune the composition-units module from the import closure.

The alternate restriction-isomorphism route to identifying an arbitrary
extension is unnecessary: local Kan representatives suffice. A temporary import
of `Mathlib.CategoryTheory.Sites.LocallySurjective` was also removed because its
required API is already available through the retained imports.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The planned étale
inverse-image/restriction isomorphism is unnecessary for both the diagonal
calculation and uniqueness. The former follows directly from naturality and
the adjunction unit; the latter follows from local Kan representatives and
separatedness. The DAG and proof docstring now describe this proved route.
The blueprint unit has no realized steps being bypassed. No new nodes,
statement changes, forced adaptations, or change records are needed.

## Second reading by F2

1. Interface preservation: compared the complete module with the shared
   repository using `diff` and the declaration comparison parser. The existing
   concrete unit definition, including its body, is byte for byte unchanged;
   the existing bijectivity theorem's signature is byte for byte unchanged.
   Only private helpers, the proof, its explanatory docstring, and proof-only
   imports differ. No change records or forced adaptations are required. PASS.
2. Proof validity: read all helpers and both injectivity and surjectivity
   arguments. Independently compiled the item cleanly with `lcompile.py`.
   Scanned for holes and forbidden declarations: none. Checked both public
   declarations with `#print axioms` in a scratch copy. The only classical
   choice in the new definitions selects the composition isomorphism from a
   proved theorem whose fixed-sheaf uniqueness clause determines it. All other
   new data are explicit constructions or adjunction transposes. PASS.
3. Split statements: none are introduced, and all private helper statements
   are proved. The local representative argument uses covering sieves, so it
   also handles the empty scheme, empty covers, and empty sets of sections;
   it never assumes a point, a nonempty cover, or a global representative.
   The adjunction construction also requires no such assumption. PASS.
4. Route and pruning: checked from the final theorem through local diagonal
   representatives and local transposes. Read the imported Kan representative
   and composition-unit theorems, searched the comparison modules with `rg`,
   and independently searched Lean Finder for equality on local generators.
   No existing result directly supplies this specified universal property;
   downstream adjunction results depend on this item and cannot replace it.
   The two public imports support existing signatures or definitions, and the
   two plain imports support proofs. The sole old proof-dependency node
   removed is `lem-weil-pbc-sets-etale-inverse-image-restriction`, reported
   above. The unit `sk-prop-sf-comparison` has empty realized statement and
   step lists; this proof bypasses no recorded unit step. PASS.
5. DAG agreement: compared the node with the repository version; only `proof`,
   `proof_deps`, and `proof_origin` changed. The dependency list is exactly the
   union of step uses and records the actual local-site, composition-unit,
   and Kan representative route. The node's Lean statement remains unchanged.
   Read Stacks Tags 0GLZ and 09XN online: the local-transpose construction and
   local pulled-back representatives follow those sources. PASS.

Second-reading changes: completed `No longer needed` by recording the removed
redundant direct composition-units import and explaining why its node remains
needed. No Lean or DAG repair was necessary. Closed 1 original hole; added 0
holes; split off 0 statements.
