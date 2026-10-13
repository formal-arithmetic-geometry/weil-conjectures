## What changed

Replaced the `sorry` in `CategoryTheory.filteredHomologyCouple_exact` with a proof from
`filteredStep_shortExact` and the Mathlib long exact homology sequence. Three private
helpers handle the index transports and derive zero composites and image-kernel
exactness. The experimental proof-only imports were removed; the module keeps only
its required public import `Sheaf.CategoryTheory.FilteredHomologyCoupleData`.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.filteredHomologyCouple_exact` (node
`lem-sp-filtered-homology-couple-exactness`). No `sorry` remains. Holes added: none.
This is a proof, not a decomposition (one hole closed, zero added).

## No longer needed

No imports, DAG dependencies, or modules are pruned relative to the repository version.
The proof-only import `Mathlib.CategoryTheory.Abelian.Exact` was removed from an
experimental candidate, not from the repository baseline. The existing required public
import supplies both the statement definitions and the long exact sequence lemmas.
The old sole proof dependency `def-sp-filtered-homology-couple-data` remains used.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked by an absent compiled `FilteredHomologyCoupleData.olean`.
That dependency is now present. Its candidate proof also needed explicit local helper
lemmas because Lean does not identify the quotient and integer-index transports under
implicit transparency during direct `simp`/`exact` application; the delivered helpers
make those transports explicit while preserving the target statement.


## Second reading by V1

1. **Unchanged interface — pass.** Compared the full module against the repository
   version. The signature of `CategoryTheory.filteredHomologyCouple_exact` is byte
   for byte identical, and the imports, existing docstring, and visibility are
   unchanged. Only its proof and three private proved helpers were added. There are
   no changed definitions, adapted modules, or change records.
2. **Kernel proof — pass.** Compiled the delivered module cleanly with `lcompile.py`.
   Compiled a scratch copy with `#print axioms` for the target and each private helper:
   all four report exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
   `sorryAx`. The delivered file contains no holes, axioms, unsafe declarations,
   opaque declarations, external implementations, or data constructions from
   unproved existence assertions.
3. **Split statements — pass (none).** No new postponed statement or node is added.
   The private helpers are fully proved index-transport specializations of Mathlib's
   three long exact sequence positions. Read `filteredStep_shortExact`, the explicit
   map definitions, and Mathlib `HomologySequence` lemmas. Substituting the helpers'
   equality hypotheses reduces their transports to identities; the target's integer
   equalities hold uniformly, including zero and negative indices. Searched local
   Sheaf and upstream sources and ran an additional Mathlib grep search for
   `homologyMap_comp|exact_iff_image_eq_kernel`; the existing Mathlib facts are used
   directly rather than restated as holes.
4. **Route and pruning — pass.** The proof takes the existing proved short-exact
   filtration sequence directly to Mathlib `homology_exact₁`, `homology_exact₂`,
   `homology_exact₃`, `δ_comp`, and `comp_δ`, then converts exactness to image/kernel
   equality. The transport helpers account for the explicit maps' indices without
   introducing a new mathematical dependency. The only public import is needed in
   the target signature. The old sole proof dependency remains used; none is pruned.
   Read `dag/units/sk-prop-av-pqf-finite.json`: its `realized` lists do not name this
   node or any replaced step, and this delivery changes no unit route or record.
5. **DAG agreement — pass.** Read the exactness node and its data dependency. The
   existing `proof` already describes exactly this long exact sequence argument,
   its integer transports, and image/kernel conversion. `proof_deps` is exactly the
   data node actually used, and `proof_origin` agrees. No node edit is required.

Second reading changed only this report: clarified that the experimental import
removal is not pruning relative to the repository, explicitly counted the one hole
closed and zero added, and recorded the independent checks. The Lean proof needed
no repair.
