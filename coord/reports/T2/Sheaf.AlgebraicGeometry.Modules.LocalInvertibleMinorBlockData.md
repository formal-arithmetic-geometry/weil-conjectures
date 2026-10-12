## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_local_invertible_minor_block_data`
in `Sheaf.AlgebraicGeometry.Modules.LocalInvertibleMinorBlockData`, preserving its
signature, visibility and docstring. Added proved private helpers for injectivity
of the selected indices, extending the indices to an equivalence, splitting a
free sheaf, and computing its matrix under restriction and coordinate changes.
Added proof-only imports of `WeilConjectures.Mathlib.AlgebraicGeometry.Restrict`
and `Mathlib.Logic.Equiv.Fintype`. Updated the existing node's proof and origin to
record the implementation of the same pivot-minor route.

The open is constructed as the basic open of the pulled-back determinant.
All basis isomorphisms come from proved finite equivalences and free-sheaf
functors. No data is obtained from an unproved existence theorem. The construction
and determinant calculation include rank zero and empty complementary factors.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_local_invertible_minor_block_data`
(node `lem-pc-local-invertible-minor-block-data`).
No holes remain in the item. No holes were added or split off. All private
helpers are proved. Single-file compilation passed with no warnings; the
required delivery dry run additionally checks axioms and the preflight.

## No longer needed

None. No original imports or planned dependency nodes were removed. No new
statement modules were introduced. The scratch proof file is outside `lean/`
and is not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The referenced literature Markdown files
are absent from this checkout; the existing theorem docstring and the unit
record retain the source argument. The proof follows that argument and uses the
already proved basic-open unit theorem instead of repeating its gluing proof.
The unit's pivot-minor route is preserved, and no interface adaptations are needed.

## Second reading by T2

1. Compared the delivered module against the repository version. The theorem signature, visibility, and docstring are unchanged byte for byte; only the proof body and proof-only imports changed. The DAG node changes only its recorded proof route and origin. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds without warnings. An axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`s, axioms, unsafe declarations, or hollow definitions in the delivered module. Verdict: pass.

3. Checked the proof route against the existing declarations and the node statement. The construction uses the basic open of the pulled-back selected determinant, proves injectivity of selected indices from the repeated-row/column determinant lemmas, extends them to finite equivalences, and computes the restricted matrix by functoriality. The rank-zero and empty-complement cases are covered by the same finite-equivalence construction. No split-off statements were added. Verdict: pass.

4. The proof uses the shortest available route below the unit: existing free-sheaf, pullback, restriction, determinant, and finite-equivalence declarations. The two added imports are proof-only and are not public. No old import or dependency node became unnecessary. Verdict: pass.

5. The unit's pivot-minor route is preserved: the open is chosen from the selected determinant, coordinate decompositions are built from the selected indices and complements, and the leading determinant is identified with the restricted minor. The DAG proof steps and dependencies record this route. Verdict: pass.

Changed the report only; no Lean declarations or statements required repair.
