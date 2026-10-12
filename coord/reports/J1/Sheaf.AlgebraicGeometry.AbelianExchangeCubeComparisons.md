## What changed

Proved `AlgebraicGeometry.Etale.exchangeCube_stalk_square` with its signature and
original definitions unchanged. Private proved helpers implement equality transport of a
mate, the two horizontal pastings and isomorphism cancellations, naturality for the
single-complex identification, and functoriality of `derivedStalkComparison`.
All work stays in `Sheaf.AlgebraicGeometry.AbelianExchangeCubeComparisons`.
Updated its node proof and proof dependencies to match the Lean proof.
The module compiles without warnings. The delivery dry run checks the axioms.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Etale.exchangeCube_stalk_square`
(node `lem-weil-pbc-abelian-exchange-cube-comparisons`). No `sorry` remains in the
module, and no hole or new module is added. This is a proof, not a decomposition.

## No longer needed

Removed the proof import `Sheaf.Paper.InverseImageStalkGerm` and the proof dependency
`lem-weil-pbc-inverse-image-stalk-germ`: the calculation only needs naturality of the
existing `upperStarCompSheafFiberIso`, not its germ formula. That node/module is
unneeded by this proof; this does not assert it is globally unreachable.
Retained `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal` for its
proved horizontal pasting law. Also removed the redundant proof import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: its
homology and single-complex comparisons are available through the retained imports.
No other planned node or module is pruned.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The saved attempt already contained the complete categorical calculation. Its
previous dry run was blocked by a missing repository module during the import-cycle
check; the current dry run passes that check. The proof uses the horizontal pasting
equalities with explicit outer squares. Equality
transport of the outer mate followed by composition with the two isomorphisms
reduces the cube calculation to their cancellation identities. Single-complex,
homology, and stalk naturality are then separate short calculations.
One map-of-identity cancellation needs `erw` because ordinary rewriting does not
match the derived category identity at reducible transparency.
No statement, definition, or interface correction was needed.

## Second reading by J1

1. Compared the delivered module and node with the repository versions. The public
   definitions and theorem signature are byte-for-byte unchanged; only proof code,
   proof metadata, and proof-only imports were changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings and contains
   no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch
   `#print axioms` check for `exchangeCube_stalk_square` reports only `propext`,
   `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the proof route and helper calculations. The private helpers are strictly
   intermediate equalities (outer horizontal pasting, stalk naturality, and insertion
   of the single-complex comparison), and the target proof uses them to prove the
   unchanged statement. No split-off statements or new nodes were added. Verdict:
   pass.
4. Checked pruning and imports. `Sheaf.Paper.InverseImageStalkGerm` and
   `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` are not
   needed by the compiled proof and were removed; the horizontal pasting import is
   still used. The node proof dependencies match the proof, and the unit route is
   retained. Verdict: pass.
5. Checked the DAG node and report against the Lean proof. The node keeps its
   statement and records the revised proof steps and dependencies; no target or
   definition was changed. Verdict: pass.

Changed only the report by adding this second-reading record; no Lean repair was
necessary.
