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

## Earlier second reading (a previous round; superseded)
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

## Second reading by N2

1. PASS. Independently diffed the only delivered Lean module against the current
   repository and compared the complete existing theorem signature as strings:
   byte-for-byte identical. Existing definitions, declaration visibility, and public
   imports are unchanged. The node differs only in `proof` and `proof_origin`.
2. PASS. Compiled the delivered module using lcompile.py (6.2 seconds, no diagnostics),
   then regenerated the scratch axiom probe from this exact delivered source and
   compiled it (6.1 seconds). The theorem uses `propext`, `Classical.choice`,
   `Quot.sound`, and inherited `sorryAx`. No local sorry or prohibited declaration
   occurs. The local boundary is explicitly cokernel.desc of the connecting arrow
   after the inverse product comparison; no definition is added.
   Clarification of the earlier report: the Roos isomorphism e₁ is not uniquely
   determined by the imported existence theorem (negating it also gives a natural
   isomorphism). Here it is eliminated only inside a proof of an existential
   proposition, whose requested boundary family is likewise not canonical. It is
   never used to define public data or an arbitrary chosen library object. The
   product and cokernel constructions retain their universal properties.
3. PASS. No split-off statements or new holes. Checked the three proved private
   helpers: projectionwise identities need no preservation assumption, and the
   cokernel exactness helper uses the epi projection and identity middle/last maps.
   Zero objects, zero arrows, and nondistinguished triples are covered without extra
   assumptions; naturality is requested only for distinguished triples.
4. PASS. Independently searched the library with cokernel/exactness and comparison-map
   terminology, and Mathlib using grep and LeanFinder through msearch.py. Found the
   existing exactness-transport and product-projection APIs used by the proof;
   no complete replacement boundary theorem or shorter route was found. Public
   imports supply the derived homology, Exact predicate, and whiskering in the
   signature; new AB4Star support is a plain proof-only import. All five old DAG
   proof dependencies are retained and used. The unit's realized statement and step
   lists do not contain this node, and its route is preserved. No modules are pruned.
5. PASS. Matched the node's proof steps and dependencies with the construction,
   long-exact-sequence transport, Roos naturality, and cokernel.map_desc calculation.
   Its statement, source, unit, chapter, and lean signature record are unchanged.

This reading changed the report's explanation of existential Roos witnesses,
regenerated the exact-source axiom probe, and normalized the node JSON indentation.
The Lean proof needed no repair. Closed: CategoryTheory.milnor_boundary_factorization;
added holes: none; split off: none.
