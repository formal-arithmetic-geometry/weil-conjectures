## What changed
Added `PopescuSmoothLiftModuloEightAux` with an intermediate theorem encapsulating the detailed Popescu polynomial construction, and proved the target theorem from it plus the singular-ideal zero-locus theorem.

## Proved and sorry left
The target `exists_popescu_smooth_lift_modulo_eight` is proved. The auxiliary theorem `exists_popescu_smooth_lift_data` remains sorry and has node `lem-weil-pbc-popescu-smooth-lift-data`.

## No longer needed
No imports removed; all existing proof dependencies are subsumed by the auxiliary construction.

## Where the brief, the DAG or earlier work was wrong
The detailed eighteen-step construction is too large for this item; it is split into the strict intermediate theorem above.

## New nodes
`lem-weil-pbc-popescu-smooth-lift-data` records the intermediate construction and its source in Stacks Lemma 07F5.

## Second reading by H1

1. Compared the delivered target module against the repository version. The theorem signature and all existing declarations are unchanged byte for byte; the only target change is replacing its proof, and the new auxiliary declaration is in a separate module.

2. Compiled both delivered modules with `lcompile.py --all`. They compile successfully. The only remaining `sorry` is the named theorem `exists_popescu_smooth_lift_data`, and it is documented and paired with node `lem-weil-pbc-popescu-smooth-lift-data`; no definitions contain `sorry`, and no forbidden declarations were added.

3. Checked the auxiliary statement against the Popescu lifting construction and the target edge cases. It is a strict intermediate construction: it supplies the same finite-presentation and compatibility data together with pointwise smoothness, which implies the target singular-ideal conclusion. The source is Stacks Lemma 07F5, and searches found no existing library theorem that provides this construction.

4. The proof follows the intended route through `exists_popescu_smooth_lift_data` and `Algebra.singularIdeal_zeroLocus`; no imports were removable, and the unit route remains represented by the existing Popescu lifting dependency and the new intermediate node.

5. The DAG node for the new theorem records the same statement, source, proof dependency, split status, module, and declaration. No target or definition was altered.

Changed after review: added this second-reading record and regenerated the required search log; no Lean proof text required repair.
