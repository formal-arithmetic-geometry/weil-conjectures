## What changed
Replaced the geometric descent sorry with a proof using the explicit split action, orbit decomposition, geometric fixed-orbit descent, and affine reconstruction. Added the algebraic reconstruction helper theorem.

## Proved and sorry left
The target theorem `affine_torsor_equivariant_descent` is proved. `affine_torsor_equivariant_descent_algebra` remains sorry as the algebraic reconstruction substep.

## No longer needed
Removed the unused import `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantOrbitProduct`; the proof uses the supplied orbit-data form.

## Where the brief, the DAG or earlier work was wrong
The original proof plan omitted the explicit split-action and orbit-data interface needed to connect geometric descent to the equivariant algebra.

## New nodes
`lem-sbc-affine-torsor-equivariant-descent-algebra` records the remaining algebraic reconstruction substep.

## Second reading by T4

1. Compared the delivered target module with the repository version. Existing theorem signatures are unchanged; the only interface addition is the documented split-off algebra reconstruction theorem and its node.
2. Compiled all five sandbox modules with `lcompile.py --all`; they compile cleanly. The only remaining sorries are the named imported geometric/action lemmas and the split-off algebra theorem listed above; no definitions contain sorry.
3. Checked the split-off statement against the concrete `FixedOrbitData` and equalizer construction. It is a true, strictly simpler orbitwise algebra reconstruction statement, with a source and proof plan in its docstring and node.
4. Pruned the proof-only imports to plain imports and verified the target proof uses the split action, geometric fixed-orbit descent, and algebra reconstruction interfaces. The target node's original route remains represented by these unit interfaces.
5. The unit route is retained: the target still constructs the explicit action, applies geometric descent, and then identifies the orbit algebra before the final Over isomorphism.

Changed the algebra theorem docstring and node statement to match the split theorem exactly, made the geometric/action imports proof-only, and added this second-reading record.

The interface change is recorded in `coord/changes/AffineTorsorEquivariantDescent-interface.md`.
