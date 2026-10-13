## What changed

Replaced the sorry in `AlgebraicGeometry.perfect_descent_common_local_models` by a
proof combining single-open eventual models. The proof applies descent separately
on W and V, takes an upper bound of the two stages, obtains their models there,
and proves that the concrete inverse-image opens cover and are compact.
The existing statement, visibility, public imports and definitions are unchanged.

Added `Sheaf.AlgebraicGeometry.PerfectDescentOpenEventualModel`, containing the
single-open descent/transport obligation. This is a strict part of the argument:
it has only one original open, supplies no second model, and asserts neither a
cover nor compactness. It isolates cartesian open identifications and derived
pullback transport, while the main module proves the common-stage and geometric
assembly. Source: Stacks Project Tag 09RF, the local-model choice and enlargement
of the index in the two-open induction.

## Proved and sorry left

Closed: `AlgebraicGeometry.perfect_descent_common_local_models`
(node `lem-pc-perfect-descent-common-local-models`). The main module has no sorry.

Added and left: `AlgebraicGeometry.perfect_descent_open_eventual_model`
(node `lem-pc-perfect-descent-open-eventual-model`). Its proof is exactly `by sorry`.

This is a decomposition: one existing hole closed, one strictly smaller single-open
hole added; net hole reduction is zero. The synchronization of stages, the cover,
compactness, and packaging of the two objects are proved in Lean. No data definition
uses a sorry or chooses an arbitrary witness from a mere existence theorem.

Edge cases: W empty gives an empty inverse-image open at every stage, with its
perfect restriction model. If W is the entire image of f, the same cartesian
identifications apply. The two original opens may be equal, disjoint or empty;
no intersection assumption is made. A non-antisymmetric directed preorder uses
functoriality and proof irrelevance, not equality of its indices. The specified
index i supplies the necessary nonempty tail. No colimit hypothesis is added.

## No longer needed

Removed direct proof imports from the main module:
`Sheaf.AlgebraicGeometry.DerivedPullbackPerfect`,
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`, and
`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`.
The main proof instead imports the single-open eventual-model module.
Those three nodes remain ingredients of the new hole's proof plan; this is a
relocation of obligations, not a claim that their modules are globally pruned.
No node or module is certified no longer needed in the targets' entire closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the existing statement or route was found.
The cartesian identifications and transport in the first two planned steps are
substantial Lean glue and are isolated in the new single-open theorem. The local
source file named by the original node was not present on this machine; the source
was read at https://stacks.math.columbia.edu/tag/09RF instead.
Lean Finder, Loogle, Mathlib grep and library searches found no existing exact
one-open eventual-model theorem. LeanSearch returned Internal Server Error, which
is recorded as unavailable. The unit `sk-thm-picard-semicon` has no realized node
for this sublemma, and the two-open induction route is preserved.

## New nodes

`lem-pc-perfect-descent-open-eventual-model` records descent and transport on a
single specified original open, with comparisons on its concrete inverse-image
opens at every sufficiently late stage. Its module is
`lean/Sheaf/AlgebraicGeometry/PerfectDescentOpenEventualModel.lean`.
The node has a source, complete proof steps, the existing dependency nodes, search
records, blueprint ancestry, and a verbatim Lean statement. The original node's
proof and proof dependencies now follow the common-stage assembly written in Lean.
There are no change records or forced adaptations.

## Second reading by Q2

1. **Interface unchanged.** Compared the delivered common-local-model module with the repository version: the existing theorem signature and all hypotheses and conclusions are byte-for-byte unchanged. The new single-open theorem is a separate declaration. Verdict: pass.

2. **Proof and axioms.** Both delivered modules compile with `lcompile.py --all`; the only remaining `sorry` is the named theorem `perfect_descent_open_eventual_model`. The common theorem proof contains no `sorry`, hollow definition, axiom, unsafe, opaque, extern, or implemented_by declaration. Verdict: pass, with the single-open theorem intentionally split off.

3. **New statement.** The single-open statement is a strict one-open component of the Tag 09RF argument: it asserts eventual stage models and transport for one specified open, while adding no cover, compactness, overlap, or colimit claim. Its edge cases include empty and coincident opens, and its preorder assumptions are exactly those of the parent theorem. The node statement matches the Lean declaration. Verdict: pass.

4. **Route and pruning.** The common theorem uses the new eventual-model theorem for each open, directedness for a common stage, and direct inverse-image cover and compactness arguments. Removed proof-only imports are `DerivedPullbackPerfect`, `DerivedPullbackComposition`, and `DerivedPullbackOpenRestrictionUniverses`; they remain dependencies of the split theorem. No unit route is bypassed. Verdict: pass.

5. **DAG and report.** The common node proof and `proof_deps` match the Lean proof, and the new node records its source, statement, proof steps, searches, and blueprint ancestry. Verdict: pass.

Changed during second reading: no Lean statements or proofs; added this review section only.

