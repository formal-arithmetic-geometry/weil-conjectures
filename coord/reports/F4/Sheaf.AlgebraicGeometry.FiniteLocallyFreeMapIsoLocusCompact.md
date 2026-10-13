## What changed

Reduced `isCompact_moduleMapIsoLocus_inter` to a single affine-frame
principal-open identity in the new module
`Sheaf.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen`. Added proof-only imports of
that module and `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`.
Existing signatures, visibility and public imports are unchanged. The second reader
corrected the compactness docstring to describe arbitrary affine refinements and
basic opens of those frames, as the actual proof does.

The private helper refines simultaneous finite free frames to affine neighbourhoods
contained in V, using the already proved source-library frame and restriction APIs.
The main proof selects a finite subcover of V, proves the required set equality
pointwise, and applies `Finset.isCompact_biUnion`.

Both delivery modules compile cleanly with `lcompile.py --all`. The required
`deliver3.py --no-push` dry run printed OK, with only the second reading reserved for
the independent reader. Nothing was pushed.

Independent scratch compiles validated the complete simultaneous affine frame
refinement and the generic finite-cover compactness argument. Scratch files are in
`scratchpad/`, outside `lean/`, and are not delivery modules. They do not replace or
compile the missing shared declaration.

## Proved and sorry left

Closed the one body hole of
`AlgebraicGeometry.Scheme.Modules.isCompact_moduleMapIsoLocus_inter`
(node `lem-sc-finite-locally-free-map-iso-locus-compact`) by a complete Lean proof from
the affine-frame identity below and existing proved frame and compactness lemmas.
The assigned module now has no direct `sorry`.

One hole is split off:
`AlgebraicGeometry.Scheme.Modules.moduleMapIsoLocus_inter_eq_basicOpen_of_free`
(node `lem-sc-finite-free-map-iso-locus-basic-open`). Its entire proof is `by sorry`.
This is a decomposition, with one upper hole replaced by one strictly local
finite-free matrix identity, not a net decrease in holes. No definition contains a
hole. The private helper contains no hole.

## No longer needed

No imports were removed. No previously planned module can be claimed pruned: the
original module imported only statement dependencies. The original direct proof
edges to `def-sc-module-map-iso-locus` and `def-pc-module-pullback` move into the new
local principal-open node; both remain needed transitively. The finite local frames,
affine refinements, determinant calculation and finite union route are retained.

## Where the brief, the DAG or earlier work was wrong

The DAG marked the affine determinant identification elementary, but no existing
Lean declaration supplied that identification. It requires constructing the matrix,
comparing tensor pullback with restriction and passing to stalks/residue fields.
The remaining matrix step is now explicitly named, sourced and documented.

The first compile attempt was blocked by a missing `ModuleMapIsoLocus.olean` in the
shared cache. A subsequent cache refresh supplied it, and the complete delivery then
compiled without edits or workarounds to the shared library or tools.

## New nodes

`lem-sc-finite-free-map-iso-locus-basic-open` states that on an affine open with two
finite free frames, the intersection of the neighbourhood-defined locus with the
open is a single basic open. It assumes no equality of ranks: unequal ranks give
D(0), rank zero gives D(1), and an empty open gives two empty sets. These edge cases
were checked mathematically before stating it. Its docstring records the matrix,
adjugate, stalk determinant and unequal residue-dimension arguments. Sources read:
Stacks Project Tag 05GD, Lemma 10.79.4(3), and Tag 0BDP, final determinant sentence.
LeanSearch was unavailable; LeanFinder and Loogle found generic compactness lemmas;
local Lean and DAG searches found no duplicate of the proposed identity.

The parent's node records the compiled reduction and keeps the same unit route.
No change record is needed because no existing interface changed.

## Second reading by F4

1. **Existing interfaces: PASS.** Compared the delivered compactness module with
   the repository using `diff` and the declaration parser. The existing signature
   is byte for byte unchanged; visibility and public imports are unchanged. Only
   proof-only imports, a proved private helper, the theorem body and the explanatory
   docstring differ. The finite-free module is new; no definition is changed and
   no change record is required.

2. **Proof and axioms: PASS as a decomposition.** Independently compiled both
   modules in dependency order with `lcompile.py --all`, without errors or warnings.
   Scratch copies with `#print axioms` for both public declarations compiled and
   showed exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The only direct hole is the named finite-free theorem reported above. Checked
   the complete frame restriction and finite-cover arguments line by line. No
   forbidden declaration or holed definition occurs. Existential frame and section
   witnesses are used only inside proofs; no arbitrary data is defined from the
   unproved existence theorem. The delivery tool additionally probes all declarations.

3. **Split-off identity: PASS.** Read the finite-free statement, its full docstring
   and its node against Stacks Tags [05GD](https://stacks.math.columbia.edu/tag/05GD)
   and [0BDP](https://stacks.math.columbia.edu/tag/0BDP). Finite free frames do give a
   matrix of sections. Equal ranks give its determinant and the adjugate inverse;
   a neighbourhood inverse gives a unit determinant in the stalk. Unequal ranks
   cannot be isomorphic over a residue field and give D(0). Rank zero gives D(1),
   and empty affine opens satisfy the equality even over the zero ring. No global
   freeness or equality of ranks is silently assumed. The statement is strictly
   local and is stronger than local compactness, rather than a renamed copy of the
   varying-rank compactness target. Independent LeanFinder search for distinguished
   determinant opens, Loogle search `Matrix.det, IsUnit`, and `rg` searches of the
   source library, Mathlib sheaf modules and `lean/` found no duplicate. Useful
   ingredients include `Matrix.isUnit_iff_isUnit_det` and
   `RingedSpace.isUnit_res_basicOpen`; the missing sheaf/matrix and pullback/restriction
   comparison is substantial and cannot be closed by applying those alone.

4. **Route, imports and pruning: PASS.** The argument follows finite local frames,
   affine refinement, the determinant identity, and finite gluing. The local hole
   remains exactly the determinant step. The two original public imports are
   statement dependencies; both added imports are proof-only and used. Tested
   removing the new module's free-sheaf import in a scratch copy: compilation
   fails with unknown `SheafOfModules.free`, confirming it is needed by the
   signature. No module is pruned. Both old direct dependency edges omitted from
   the parent are listed under `No longer needed` and retained in the local node.
   Read `dag/units/sk-prop-av-cube.json`: its `realized.statement` and step list are
   already empty. This pre-existing bookkeeping gap is not repaired by this item;
   the unit, its sole cube-theorem step, and its route are unchanged.

5. **DAG agreement: PASS.** Compared the parent's node with the repository: only
   `proof`, `proof_deps`, and `proof_origin` changed. Its steps describe the proved
   helper, principal-open application, finite subcover and set equality faithfully.
   Its dependencies are the union of the steps' uses. The new node has the required
   source, complete proof sketch, statement/dependency records, search records,
   creation/blueprint metadata and exact Lean statement. It does not depend on the
   parent, so the reduction introduces no dependency cycle.

**Second-reading changes:** corrected the compactness docstring's claim that the
chosen affine frames are principal opens of V; the proof only needs arbitrary
contained affine opens. Added this independent review and recorded its searches.
No proof or statement was rewritten. One upper hole is closed and one lower hole
is added, a decomposition with net zero holes closed.
