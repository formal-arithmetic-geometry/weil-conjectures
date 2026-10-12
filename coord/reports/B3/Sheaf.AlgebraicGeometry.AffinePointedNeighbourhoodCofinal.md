## What changed

Proved `AlgebraicGeometry.Scheme.affinePointedNeighbourhoods_initial_and_final_op`
in `lean/Sheaf/AlgebraicGeometry/AffinePointedNeighbourhoodCofinal.lean`, preserving
its signature and existing docstrings. Added the proof-only import
`Mathlib.CategoryTheory.Filtered.Final`.

For each object of the category of elements, the proof unpacks its geometric point,
chooses an affine open immersion containing its image, and lifts the geometric point
along that immersion. The composite to the base is étale by existing instances.
It constructs the affine object and the point-preserving refinement explicitly.
Mathlib's `Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful` proves
initiality using the ambient cofiltered instance and the full, faithful inclusion.
The opposite inclusion is final by `Functor.final_op_of_initial`.

All three planned dependency nodes are Mathlib leaves, and their recorded
Mathlib declarations supply this proof. The node's proof route and dependencies
remain accurate; no node changes are necessary. The unit record `sk-prop-h2`
has no realized statement or step assigned to this node, and no unit route is bypassed.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.Scheme.affinePointedNeighbourhoods_initial_and_final_op`
(node `lemma-weil-pbc-affine-neighbourhood-cofinal`).

No sorry remains in the delivered module, and no new theorem or module is added.
The local compile completed without errors or warnings.

## No longer needed

None. Both existing public imports are retained for the statement's geometry and
initial/final functor classes. The added proof import supplies the initiality
criterion. All three original proof dependency nodes are still used through
Mathlib: `lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`,
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, and
`lem-weil-pbc-colimit-initial-full-subcategory`. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The initial module had no proof-dependency imports,
but the relevant dependency declarations are Mathlib leaves rather than missing
Sheaf modules. The affine-refinement construction follows the already proved
construction in `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.

Searches run: LeanFinder for the initiality criterion for a weakly initial full
subcategory of a cofiltered category (exact match); Loogle for the criterion's
name (exact match); local ripgrep through Sheaf, WeilConjectures, and Mathlib's
étale-point and final-functor files. No duplicate specialized theorem was found.
The proof works for arbitrary base schemes, including nonaffine bases: only the
chosen neighbourhood is shrunk, and no separatedness hypothesis is used.

## Second reading by B3

1. PASS. Compared the delivered module with the repository by `diff -u`: the
   existing declaration signature and docstrings are byte for byte unchanged.
   Only the proof body and a plain proof-only import were added. No definitions,
   target statements, or externally visible imports changed.
2. PASS. Compiled the delivered file locally without errors or warnings. A scratch
   copy of the delivered file with `#print axioms` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. The delivered module contains no `sorry`
   and none of the prohibited declarations or attributes.
3. PASS. There are no split-off statements or new nodes. Independently searched
   Mathlib using msearch grep for affine cofinality and the full-subcategory
   criterion, and searched both Lean roots for specialized affine initiality.
   Read Mathlib's `pointSmallEtale` affine-refinement construction and the exact
   initiality criterion. No shorter specialized theorem was found. For an affine
   base point the base itself supplies an affine neighbourhood; for a nonaffine
   base only the neighbourhood is shrunk. An empty base admits no such geometric
   point, so causes no missing case. The lift uses that the spectrum of a field
   is a singleton, and preserves the original geometric point over the base.
4. PASS. The proof constructs affine refinements and applies the existing
   cofiltered/full/faithful criterion, then the opposite finality instance.
   Both original public imports provide names in the statement; the additional
   Filtered.Final import is proof-only. All three old proof dependencies are
   used through their recorded Mathlib matches, so `No longer needed: None` is
   complete. Read `dag/units/sk-prop-h2.json`: this node is not assigned any
   realized unit statement or step, and no unit route is bypassed.
5. PASS. Read the item's node and the three dependency nodes in
   `sec-proper-base-change`. Their Mathlib matches are exactly the affine-open
   and lift lemmas, ambient cofiltered instance, and full-subcategory initiality
   criterion used here. The existing proof, proof_deps, and proof_origin agree
   with the delivered argument; no node edits are needed.

Second reading changed only this report, adding the independent checks above.
The Lean proof was correct and required no repair.
