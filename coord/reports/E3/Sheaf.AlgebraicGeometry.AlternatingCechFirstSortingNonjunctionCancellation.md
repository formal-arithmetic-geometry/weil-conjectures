## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.cechFirstSortingNonjunctionCancellation`
with a complete Lean proof from two strictly smaller labelled-deletion identities.
The statement, universes, binders, visibility and existing docstring are unchanged.

The new proof-only imports are
`Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingPrefixCancellation` and
`Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingTailCancellation`.
Each new module states one pure finite-sum identity, for an arbitrary function from
endomaps of the original finite label set to an abelian group. Neither mentions
schemes, presheaves, restriction maps, cochains, or the differential.
The prefix statement only covers deletions before the junction; the tail statement
only covers the complementary nonjunction deletions. Incoming terms are partitioned
by the strict lexicographic order of (value, original position).

The item's proved private helper `sortingRestriction_comp` identifies composite
restriction maps using the fact that the category of scheme opens is thin and
presheaf functoriality. The main proof moves integer scalars through restriction
homomorphisms, expands the differential and homotopy, partitions both fourfold sums,
applies the two new identities, and rearranges the resulting four terms.
All three modules compile cleanly together through `lcompile.py --all`.

The finite combinatorial identities were independently checked by integer
coefficients of every composite label map for 212 tuples: lengths 2 through 5,
all binary-valued tuples (including constant tuples), and all permutations of
pairwise distinct values. This includes the smallest degree, first and last
prefixes, reversed orders, and repetitions. Empty I admits no tuple of these lengths;
a trivial coefficient group makes both identities zero. These checks support the
formulation and signs; the two generic combinatorial proofs remain obligations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.cechFirstSortingNonjunctionCancellation`
(node `lem-pc-alternating-cech-first-sorting-nonjunction-cancellation`).
There is no sorry left in the item's module.

Added two holes, each the whole proof of a public named theorem with a source,
a complete labelled-deletion proof in its docstring, and a matching node:

- `AlgebraicGeometry.Scheme.cechFirstSortingPrefixCancellation`
  (`lem-pc-alternating-cech-first-sorting-prefix-cancellation`).
- `AlgebraicGeometry.Scheme.cechFirstSortingTailCancellation`
  (`lem-pc-alternating-cech-first-sorting-tail-cancellation`).

This is a decomposition: one hole closed, two holes added (net -1), with the
categorical restriction calculation and the sum-combination proof completed.
No definition, axiom or arbitrary chosen witness was added.

## No longer needed

Removed the redundant direct proof import `Sheaf.CategoryTheory.SiteCechComplex`;
the public sorting-operator import already exposes it and its definitions are
still used. No module or existing DAG node is pruned from the target closure.
The original dependencies `def-pc-alternating-cech-sorting-operators` and
`def-weil-pbc-site-cech-complex` remain needed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node has one long proof step using only definitions. Its declared
proof dependencies contain no labelled-deletion or permutation-restriction
identity to apply. The missing prefix and tail portions are now explicit separate
obligations. No original mathematical statement was found false or changed.

Read Stacks Tag 01FM, equation `cohomology-equation-first-homotopy`, and its
surrounding definitions of the stable and partial permutations. The source
explicitly omits the verification; the new nodes spell out the required two
bijections, sign restriction formulas, inverse insertion operations and edge cases.

The prescribed searches ran through `msearch.py`: LeanFinder returned general
homotopy and alternating-map facts; Loogle returned basic permutation sign facts;
grep found `Equiv.Perm.decomposeFin.symm_sign` and related ingredients but no
matching sum identity. LeanSearch returned Internal Server Error and is recorded
as unavailable. Blueprint searches for sorting and permutation found no duplicate
of either new identity. `blueprint_refs.py ancestor` returned None for the item
(module-style created.item records break that walk), so the new nodes inherit
the item's existing recorded ancestor `lem-pc-projective-space-cohomology-bound`
and prepend the item node to its recorded via chain.

## New nodes

`lem-pc-alternating-cech-first-sorting-prefix-cancellation`, in
`lean/Sheaf/AlgebraicGeometry/AlternatingCechFirstSortingPrefixCancellation.lean`,
is the prefix-deletion part. Restriction removes j = sigma r with r < a and lowers
the incoming prefix length to a - 1. The matching incoming deleted label precedes
the remaining junction in stable labelled order; its coefficient has opposite sign.

`lem-pc-alternating-cech-first-sorting-tail-cancellation`, in
`lean/Sheaf/AlgebraicGeometry/AlternatingCechFirstSortingTailCancellation.lean`,
is the complementary tail-deletion part. Nonjunction deletion with not r < a
forces r > a. Restriction keeps the prefix length a, and the incoming deleted
label follows the junction in stable labelled order; its coefficient has opposite sign.

The item's proof, proof_deps and proof_origin are updated to match the Lean reduction.
Both new nodes inherit its chapter and unit. No change record is required:
existing public signatures, definitions and visibility are unchanged.

## Second reading by E3

1. Compared the delivered item module with the repository version. The target
statement and all existing declarations are byte-for-byte unchanged; only the
proof and its proof-only imports changed. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`. The item has
no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the only
remaining sorries are the two explicitly named split-off theorems. The
restriction helper uses thinness of scheme opens and functoriality, and the
main rearrangement typechecks. Verdict: pass.

3. Rechecked the two split-off labelled-deletion statements against the stable
label order, prefix and tail cases, repeated values, and boundary cases. Their
docstrings give the inverse deletion/insertion argument and sign calculation;
their DAG nodes and declarations match exactly. Searches found no existing
duplicate. Verdict: pass.

4. The proof follows the unit route through the outgoing/incoming partition and
the two labelled-deletion identities. The direct `SiteCechComplex` proof import
was removed because it is exposed by the sorting-operator import; no other
unused import or reachable node was found. Verdict: pass.

5. Checked the DAG proof steps, dependencies, origins, and both new node records
against the Lean proof and report. The realized unit route is preserved and no
statement or definition was changed. Verdict: pass.

Changed only the proof imports/proof body, added the two required split modules
and nodes, and added this second-reading record.
