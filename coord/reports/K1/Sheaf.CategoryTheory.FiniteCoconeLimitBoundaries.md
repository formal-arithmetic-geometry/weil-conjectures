## What changed

`Sheaf.CategoryTheory.FiniteCoconeLimitBoundaries` now proves
`CategoryTheory.BigradedExactCouple.finiteCocone_limitBoundaries` from the finite-boundary
formula in the new proof-only import `Sheaf.CategoryTheory.FiniteBoundaryAlphaKernel`.
The signature and existing docstrings are unchanged. A proved private `alphaIter_cocone`
helper iterates the cocone equation. Its transport argument is adapted from the existing
private helper in `Sheaf.CategoryTheory.NormalizedGradedFiniteKernel`, avoiding that
module's unrelated half-plane hypotheses and dependencies.

The proof bounds every finite boundary by the proposed value. It then selects
`r = (p - a).toNat`, cancels the invertible tail map in its kernel, and obtains that
value as an actual finite boundary. Both inequalities follow from `L.B_lub`.
The parent node now records this route. No existing interface was changed.

## Proved and sorry left

Closed: `CategoryTheory.BigradedExactCouple.finiteCocone_limitBoundaries`
(node `lem-sp-finite-cocone-limit-boundaries`), by a complete Lean proof from the
finite-boundary formula. The private cocone helper is fully proved.

Added and left: `CategoryTheory.BigradedExactCouple.finiteBoundary_alphaKernel`
(node `lem-sp-finite-boundary-alpha-kernel`), in the new module of its own.
This is a decomposition: one upper hole closed and one strictly smaller finite
formula left, with net zero holes closed. The finite formula has no cocones, no
invertible-tail hypothesis and no limiting subobjects. Its full induction and
refinement argument is in its docstring and node. No sorry remains in the item.

Edge cases: at r=0 the alpha iterate is invertible and the finite boundary is zero;
when p<=a the chosen r is zero, and the cocone map is already invertible. Negative
p-a is handled by Int.toNat and omega. A zero category and invertible alpha also
give zero on both sides. There is no regularity or upper-tail assumption.

Both delivered modules compile with lcompile.py in import order, without warnings.

## No longer needed

No imports removed and no modules pruned. The parent proof no longer directly uses
`lem-sp-derived-couple-image-prefix` or `lem-sp-abelian-refinements`; both remain
needed by the new finite-boundary node's induction. `def-sp-exact-couple` remains
available through the statement dependency `def-sp-convergence`.

## Where the brief, the DAG or earlier work was wrong

The existing proof-dependency declarations give derived image inclusions and the
refinement calculus, but none states the finite-boundary identity that is step 1
of the parent's plan. That step is now a separate item. The generic finite-cycle
kernel presentation requires a following D term to vanish and does not supply this
formula without extra hypotheses; the finite-cocone stationarity theorem likewise
requires an upper zero tail, which the present theorem does not assume.

The local Stacks homology.tex is absent. Tags
[011T](https://stacks.math.columbia.edu/tag/011T) and
[0AMJ](https://stacks.math.columbia.edu/tag/0AMJ) were read online; they state precisely
the ungraded and shifted finite-boundary formulas, respectively. Stacks omits the
induction proof; the expanded proof is marked agent-written. LeanSearch returned
an internal server error, recorded as unavailable; LeanFinder, Loogle and Mathlib
grep found no exact match. Searches of both library roots and the DAG likewise
found no already stated hypothesis-free finite-boundary formula. Blueprint searches
for finite boundaries and Tag 011T returned no matching imported nodes. The parent
unit's realized entries are empty; the finite-tail route of the parent is retained.

## New nodes

`lem-sp-finite-boundary-alpha-kernel`, in
`dag/nodes/sec-abelian-varieties/lem-sp-finite-boundary-alpha-kernel.json`, states the
finite-boundary induction only (step 1 of the parent), with a new module
`lean/Sheaf/CategoryTheory/FiniteBoundaryAlphaKernel.lean`. It inherits the parent's
chapter, unit and blueprint ancestry. No change records are needed.

## Second reading by K1

1. **Interfaces — pass.** Read the complete diff against the repository module.
   The existing theorem signature is byte-for-byte identical, as is its docstring.
   The only additions are the private proved cocone helper, a plain proof import,
   and the replacement proof. No existing definition, visibility, hypothesis or
   conclusion changes. No change record is required.
2. **Proof and axioms — pass, conditional on the listed finite formula.** Compiled
   both delivered modules in import order with lcompile.py, without warnings.
   Scratch copies with explicit `#print axioms` show only propext, Classical.choice
   and Quot.sound for alphaIter_cocone; the parent and finiteBoundary_alphaKernel
   also use sorryAx, as expected for the remaining named finite-boundary theorem.
   That theorem is the sole textual sorry in the delivery. There are no definitions
   or prohibited declarations added. Checked both directions of the LUB argument,
   the cocone transport induction, and cancellation of the monomorphic tail factor.
3. **Split statement — pass.** Independently read Stacks Tags 011T and 0AMJ online
   and checked the library's type-zero g, incoming differential, derived-D indexing
   and tower successor formulas. The finite formula has the correct outgoing
   iterate and page offset. At r=0 it is zero on both sides; at r=1 exact_alpha
   identifies the incoming differential image with initialG of ker alpha. Zero
   couples and invertible alpha also give zero. The refinement induction in the
   docstring explains both inclusions, the old-boundary correction and descent.
   It requires no cocone or tail and is strictly the finite part of the parent
   argument, not a restatement. Independent LeanFinder search for “spectral sequence
   boundary subobject equals image of annihilator of iterated transition morphism”
   returned generic complex/Moore-complex lemmas, not this identity. Loogle search
   for “kernelSubobject_comp” was unavailable (recorded by msearch.py). Alternate
   grep searches on both library roots and Mathlib found no duplicate finite formula.
   Closing this general induction would require substantial new representative-map
   infrastructure, rather than a few-minute application of an existing theorem.
4. **Route and pruning — pass.** The parent uses the finite formula, elementary
   kernel containment/cancellation and B_lub; both imports are needed and the new
   one is correctly proof-only. The old direct proof dependencies no longer used
   are def-sp-exact-couple, lem-sp-derived-couple-image-prefix and
   lem-sp-abelian-refinements: the first remains transitive through convergence,
   and the latter two belong to the finite formula's future proof, as already
   reported above. No import or module is pruned. The unit realized arrays are
   empty and unchanged; the finite-boundary then lower-tail stabilization route
   is preserved. One hole closed and one added is a decomposition, net zero.
5. **Nodes — pass.** Compared the parent JSON: only proof, proof_deps and
   proof_origin differ. Its new dependency union matches the actual proof.
   Read the new node and its referenced image-prefix/refinement nodes: its Lean
   statement matches the new module verbatim, and its source, full proof plan,
   dependency union, search records, ancestry, chapter, unit, created record and
   Lean record are present. The future finite induction's dependencies are retained
   on that node, rather than falsely counted as pruned.

Second reading changed only this report: added the independent checks, axiom
results, complete old-dependency accounting and the explicit net-zero verdict.
No Lean repair was necessary.
