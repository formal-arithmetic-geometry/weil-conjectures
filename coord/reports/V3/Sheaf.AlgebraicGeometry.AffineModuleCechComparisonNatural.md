## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleCechComparison_natural_affine`.
The proof specializes `cechComparisonMapNaturality` in degree `p`, chooses the
canonical comparison maps for `F` and `F'`, and uses
`moduleCechComparison_isIso_of_affine` to package them as isomorphisms.  The
naturality square is then conjugated by the inverse of the source comparison.
Removed the unused proof import `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`.
The node proof dependencies were pruned to the two declarations actually used.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.Modules.moduleCechComparison_natural_affine`
(node `lem-sc-cech-comparison-natural`).  No `sorry` remains and no new holes
were added.

## No longer needed

Removed import `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`.
The node `lem-pc-cech-computes` and its module are no longer needed by this
proof; the proof uses only `lem-sc-cech-comparison-map-naturality` and
`lem-sc-cech-comparison-map-iso-affine`.

## Where the brief, the DAG or earlier work was wrong

The planned second step included `lem-pc-cech-computes`, but the affine
isomorphism theorem already supplies exactly the needed comparison isomorphisms.
No statement or target signature was changed.

## Second reading by V3

1. Compared the sole delivered Lean module against the repository with `diff -u`.
   The existing theorem signature and all definitions and docstrings are byte-for-byte
   unchanged. Only its proof and one plain proof import changed; no change record is needed.
2. Compiled the delivered module with `lcompile.py --all`: exit 0, no warnings.
   No local `sorry`, axiom, unsafe, opaque, extern or implemented_by occurs. A scratch
   copy with `#print axioms AlgebraicGeometry.Scheme.Modules.moduleCechComparison_natural_affine`
   compiled and reported only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Thus the original local hole is closed, but imported open proofs remain; this is
   not an axiom-free completion of the import closure. The chosen comparison maps
   are local witnesses in a theorem proof, not data of a new definition, and their
   characterizing equation determines them uniquely because alpha and the resolution
   identification are invertible.
3. No statements were split off and no new nodes or holes were added. Checked the
   types of the existing naturality and affine invertibility declarations: the first
   supplies canonical comparisons and their commuting square, and the second applies
   to exactly those comparisons. Degree zero, zero or identity morphisms, and an empty
   indexing family on the empty scheme require no extra assumption or exception.
4. Read the proof from the target downward and searched the library's Cech naturality
   declarations and the upstream affine Leray comparison. The upstream Nonempty linear
   equivalence does not provide the required IsModuleCechComparison witnesses; the
   degree-one naturality theorem is only a specialization. The existing two-dependency
   reduction and Mathlib inverse-cancellation lemma are sufficient. All remaining
   imports are needed, and No longer needed lists the sole removed old proof dependency
   and import. The unit sk-thm-picard-duality's route is preserved: this is a reduction
   within its Cech comparison subargument. Its realized arrays are already empty in
   the repository; this pre-existing bookkeeping gap is not repaired by this item.
5. Compared the node with the repository: only proof and proof_deps change, and
   proof_origin remains Stacks 01EQ/01XD. The two proof dependencies match the two
   library theorems used; there are no new nodes requiring schema checks.

Second-reading changes: clarified the node's second proof step to describe the actual
packaging and inverse cancellation, removing its stale textual reliance on the pruned
abstract Cech-computes theorem. No Lean repair was needed. Closed one original hole,
added zero holes; no decomposition or split-off statement.
