## What changed
Proved `CategoryTheory.milnor_boundary_factorization` using derived-category product
preservation, the Roos cokernel comparison, long exact homology sequences, and explicit
cokernel descent. Added three private proved helpers for comparison of transitions,
comparison naturality, and exactness after cokernel descent. Added the proof-only
`Mathlib.Algebra.Category.Grp.AB` import. Updated the existing node's proof and
proof_origin to describe the Lean argument; proof_deps remain unchanged.

## Proved and sorry left
Closed: `CategoryTheory.milnor_boundary_factorization` (one of one original holes).
Added: none. Split off: none. No sorry remains in the item.
The proof depends on the existing open declarations
`CategoryTheory.derivedCategory_countableProducts_and_towerLimit` and
`CategoryTheory.derivedLimitRoosAbelianGroups`; these are not closed by this delivery.
The axiom check reports only `propext`, `Classical.choice`, `Quot.sound`, and inherited
`sorryAx` from existing open dependencies. This closes the item's hole, not its entire
import closure.

## No longer needed
Kept the existing public imports, including the module supplying the Exact predicate
in the signature. Removed the worker's redundant proof-only import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` (already available through
existing imports). No old proof_deps node is unused; no DAG dependency module is pruned.

## Where the brief, the DAG or earlier work was wrong
The naturality step requires explicit use of `cokernel.map_desc` and comparison-map
naturality; the original plan did not detail these API steps. The first report omitted
the closed declaration name, inherited open dependencies, and the dependency record.

## Second reading by N2
1. PASS: compared the delivered module with the repository using diff and extracted
   the existing theorem signature; it is byte-for-byte identical. No existing definition
   or statement changes, no change records, and no other delivered Lean modules.
2. PASS: locally compiled the module without errors or warnings. A scratch copy with
   `#print axioms CategoryTheory.milnor_boundary_factorization` reports only the three
   standard axioms and inherited `sorryAx`. No local sorry, axiom, unsafe, opaque,
   implemented_by, extern, or hollow definition. The boundary is constructed by cokernel
   descent; the imported inverse comparisons are determined by their isomorphism laws.
3. PASS: no split-off statement or new hole. Checked the three private proved helpers:
   projection identities, cokernel epimorphism cancellation, and exactness transport.
   Zero groups/maps and nondistinguished triangles introduce no extra assumptions;
   the family is zero in the latter case and its conditions apply only when distinguished.
4. PASS: searched the library and Mathlib with projection-comparison, cokernel-exactness,
   and epimorphism-factorization terminology; independent LeanFinder and Loogle searches
   are recorded in searches.jsonl. No complete existing boundary theorem was found.
   The proof uses the planned product theorem, Roos comparison, and Mathlib exact sequence;
   no old proof_deps can be dropped. The unit's realized record is unchanged (this node
   is not a recorded unit statement or step). Reduced imports as listed above.
5. PASS: reviewed the node's statement, source, proof_deps and Mathlib leaves against the
   Lean construction. All five old proof dependencies are used. Updated its proof steps
   and proof_origin to document the actual construction and naturality calculation.

Second reading changed: removed one redundant new proof import, synchronized the proof record, and expanded
this report with explicit hole accounting and verification results. The proof itself
needed no repair.

Delivery check: the first dry run required an interface-change record for replacing
the existing public ShortExact import by Exact. Restored that existing public import;
the redundant new proof-only Products import remains removed.
