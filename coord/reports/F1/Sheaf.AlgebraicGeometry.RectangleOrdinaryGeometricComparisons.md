## What changed

Proved `rectangle_ordinary_geometric_comparisons` by combining a proved upper
pullback comparison with a strictly smaller direct-image/pasting obligation.
Its existing signature is unchanged. Added the modules
`RectangleOrdinaryGeometricPullback` and `RectangleOrdinaryGeometricDirect` and
matching DAG nodes. The pullback theorem needs neither compactness nor the
ordinary base-change isomorphism hypotheses. It constructs the canonical
comparison by fully faithful restriction and proves the equivalence using the
inverse iterated pullback isomorphism.

Explicitly typed identity-comparison extraction avoids the earlier compile
failure from destructuring a large nested existence statement. Local
irreducibility keeps the derived pullback construction folded. The proof uses
no new data chosen from an unpinned existence theorem: the composition family
is pinned by its derived universal property, and the identity comparison is
used only to prove an equivalence proposition. All three modules compiled
within the required 60-second limit.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.rectangle_ordinary_geometric_comparisons`, node
`lem-sc-rectangle-ordinary-geometric-comparisons`. The new
`AlgebraicGeometry.rectangle_ordinary_geometric_pullback` is completely proved,
node `lem-sc-rectangle-ordinary-geometric-pullback`.

Added exactly one hole:
`AlgebraicGeometry.rectangle_ordinary_geometric_direct`, node
`lem-sc-rectangle-ordinary-geometric-direct`. It constructs p and b and proves
ordinary inverse-square pasting for a fixed canonical s and an already proved
pullback equivalence. This is a decomposition (one upper hole closed, one lower
hole added), not a claim of net hole reduction. No sorry remains in the original
module or the pullback helper; none occurs in a definition or private helper.

## No longer needed

Removed the original module's direct proof imports
`Sheaf.AlgebraicGeometry.DerivedBaseChangePasting` and
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`; their nodes
`lem-pc-derived-base-change-pasting` and
`lem-pc-ringed-spaces-derived-direct-image-composition` are needed by the direct
helper instead. They remain in the import closure, so no whole module is
claimed pruned. The pullback helper needs neither of these proof modules.
All original geometric dependencies remain needed through the two helpers.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had no DAG nodes for its two new modules and used the same
blueprint tag and unspecialized docstring on both. It also repeated a large
direct-helper application three times. This repair provides distinct nodes and
complete specialized proofs in words, proves the upper comparison outright,
and combines existential results once each. The unit route is unchanged: its
realized lists contain no node bypassed here. Empty schemes, zero objects and
identity base maps need no exclusions.

## New nodes

`lem-sc-rectangle-ordinary-geometric-pullback` records the proved construction
and equivalence on the full quasi-coherent subcategories from Tag 0D5S and
Mathlib's iterated pullback isomorphism.

`lem-sc-rectangle-ordinary-geometric-direct` records the remaining direct-image
comparison and inverse ordinary pasting argument, with sources Tags 08HY,
0ATM, 0D5S and 0D5T. It assumes a fixed canonical upper comparison and its
proved equivalence, and concludes only p, b and the compatibility identity.

No existing definition or interface was changed; no forced adaptation or
change record is required.

## Second reading by F1

1. **Visibility and unchanged interfaces.** Compared the delivered comparison module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and the proof body differ. The two helper modules and their DAG nodes are new delivery files.

2. **Proof and axioms.** Compiled the pullback, direct, and comparison modules with `lcompile.py`. The pullback theorem has only `propext`, `Classical.choice`, and `Quot.sound`; the comparison theorem inherits the single named `sorry` in the direct helper. No forbidden declarations or `sorry` in definitions occur.

3. **Split statements.** Checked both helper statements against their docstrings and nodes. The pullback helper is fully proved and removes the upper geometric construction from the open target. The direct helper is a strictly lower obligation: it takes the already supplied canonical comparison and equivalence and concludes only the remaining p,b identity. Its sole `sorry` is named, sourced, and represented by `lem-sc-rectangle-ordinary-geometric-direct`; no duplicate library statement was found.

4. **Pruning and route.** The comparison proof uses both helpers exactly as written. The removed direct proof imports are no longer needed by the comparison module itself; they remain imports of the direct helper. The unit route and realized nodes are unchanged, and no bypass of the unit-level construction was introduced.

5. **DAG agreement.** Matched declarations, signatures, proof steps, `proof_deps`, and `proof_origin` for all three nodes. The new nodes include source, searches, creation metadata, unit/chapter, and Lean records; the comparison node records the new helper route and its one decomposition.

I changed only the comparison proof/imports, added the proved pullback helper and the named direct helper, added their DAG nodes, and appended this review record. No statement or definition was changed.
