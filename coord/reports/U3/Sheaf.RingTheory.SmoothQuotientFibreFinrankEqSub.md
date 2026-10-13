## What changed

Proved `Algebra.smooth_quotient_fibre_finrank_eq_sub` in
`Sheaf.RingTheory.SmoothQuotientFibreFinrankEqSub` with its signature and public
imports unchanged. Added proof-only imports of
`Mathlib.RingTheory.Kaehler.TensorProduct` and
`Mathlib.LinearAlgebra.TensorProduct.Prod`.

The proof splits the conormal sequence using Mathlib's formally smooth criterion,
identifies polynomial differentials with a rank-n free module, and extends scalars
to the chosen residue field. The conormal basis has rank c. Product rank additivity
and the differential base-change equivalence give the required subtraction.
The residue field's C-module structure is explicitly the one induced by the
composite C -> F -> K; this avoids a conflicting automatically inferred action.
The node copy now records these concrete Mathlib steps. The unit route is unchanged.

## Proved and sorry left

Closed: `Algebra.smooth_quotient_fibre_finrank_eq_sub`
(node `new-smooth-quotient-fibre-finrank-eq-sub`), the module's only sorry.
Added: none. Sorries left in the delivered module: none.
This is a complete proof from proved Mathlib declarations, not a decomposition.
Local compilation passes without warnings; the delivery dry run checks axioms.

## No longer needed

No original imports, nodes, or modules were removed. No Sheaf proof dependency is
needed: the node already had an empty proof-dependency list. In particular this
proof does not import its parent `SmoothQuotientFibreFinrankAdd` or its sibling
`SmoothQuotientFibreFinrankAddLe`, avoiding a cycle through the parent.
No new intermediate theorem or module is needed.

## Where the brief, the DAG or earlier work was wrong

The node's single proof step did not name the Mathlib declarations implementing
the argument. All the required splitting, bases, dimension additivity, and
base-change equivalences already exist in Mathlib. The updated proof records them.
No mathematical statement or definition was changed. The argument also covers
c = 0 and n = 0; the chosen prime q ensures its residue field is nontrivial.
If the fibre is the zero ring, there is no such prime q.

## Second reading by U3

1. PASS: Compared the only delivered Lean module and node with the repository
   using `diff -u`. The existing theorem signature and docstring are byte for
   byte unchanged; no definition or public import changed. Only its proof and
   two plain proof imports changed. There are no change records or new modules.
2. PASS: Compiled the module with `lcompile.py --all`, without errors or
   warnings. An independent scratch copy with `#print axioms
   Algebra.smooth_quotient_fibre_finrank_eq_sub` compiled and reported exactly
   `propext`, `Classical.choice`, and `Quot.sound`. There are no remaining
   sorries, forbidden declarations, or data definitions in the delivered module.
   The local scalar actions use the actual composite C -> F -> K; the final
   `change` checks that the computed rank is that of the original statement.
3. PASS: No statements were split off or newly introduced. Checked c = 0 and
   n = 0 against the rank identity c + d = n; n = 0 forces c = d = 0.
   A zero fibre has no prime q, so creates no exception. No unproved existence
   theorem is used to choose data.
4. PASS: Independently searched with LeanFinder for cotangent dimension of a
   smooth polynomial quotient, and with `msearch.py grep` and `rg` for
   differential finrank formulas in Mathlib and both library roots. The standard
   smooth rank lemmas require a submersive presentation absent from these
   hypotheses, and are not a shorter route. The existing parent uses this item,
   so importing it would be circular. Both added imports supply concrete
   equivalences used in the proof and remain plain imports. The old proof_deps
   list is empty, hence the pruning report is complete. Inspected
   `dag/units/sk-thm-p1.json`: this item is below its realized statements and
   steps, none of which is bypassed or changed.
5. PASS: The three updated node steps follow the actual splitting, tensor
   product ranks, and differential base-change proof. Empty proof_deps agrees
   with its use of proved Mathlib results only. Checked the source online:
   [07CH](https://stacks.math.columbia.edu/tag/07CH) supplies the split conormal
   sequence; [07CG](https://stacks.math.columbia.edu/tag/07CG) supplies the
   relative complete-intersection fibre dimension context. No new node requires
   validation.

Second reading changed only this report; the Lean proof and node needed no repair.
