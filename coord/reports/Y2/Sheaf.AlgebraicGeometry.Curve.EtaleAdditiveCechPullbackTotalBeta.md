## What changed
Proved `AlgebraicGeometry.Scheme.Modules.additiveCech_pullback_total_beta` with its signature unchanged. The proof applies the total-summand specification at `(n,0)`, projects to each tuple, evaluates the augmentation equation, and uses naturality of `J.ι`. A proved private helper identifies pullback on open-subscheme functions with `g.app` under `restrictFunctorΓ.inv`. The final coordinate calculation uses the supplied hypothesis, naturality of `g.app`, and cancellation of the mutually inverse restrictions between categorical products and intersections. No public imports or definitions changed.

## Proved and sorry left
Closed the sole original hole in `AlgebraicGeometry.Scheme.Modules.additiveCech_pullback_total_beta` (node `lem-pbc-etale-additive-cech-pullback-total-beta`). No holes added; no `sorry` remains in the delivered module. The private helper `restrict_pullback` is also proved. The proof uses definitions and proved naturality lemmas, rather than the holed total-map existence theorem. Local compilation passes without warnings.

## No longer needed
No original imports, nodes, or modules were removed. The existing DAG route is retained. No new nodes or intermediate obligations are required. Removed the unchanged dependency copy left by the earlier attempt from the delivery sandbox.

## Where the brief, the DAG or earlier work was wrong
The previous attempt had left an inline `sorry` after total-summand reduction and reported that as a tool failure. The actual remaining issue was a coordinate proof. It is now completed. The categorical product of opens is not definitionally the intersection; the proof cancels its restriction isomorphism instead of assuming definitional equality. Empty tuple families require no special case because product extensionality is vacuous; empty opens and degree zero obey the same naturality identities.

## Second reading by Y2
1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof and a private helper were added.
2. Compiled the module with `lcompile.py`; it passes without warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The proof introduces no additional holes.
3. Checked the theorem statement and proof route against the existing DAG node and searched the library for duplicate declarations. The statement is unchanged, and no split-off statement or new node was added.
4. Checked pruning and imports. The proof uses the existing `EtaleAdditiveCechPullbackTotalMap` import and the DAG route through the total-map specification; no import or dependency can be removed.
5. Checked the unit route and edge cases described by the node. The `(n,0)` summand, tuplewise limit extensionality, restriction naturality, and supplied coordinate hypothesis establish the beta equality, including degree zero and empty tuple families.

Changed only the proof body and its private `restrict_pullback` helper; no public interface, definition, node, or import was changed.
