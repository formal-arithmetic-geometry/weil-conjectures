## What changed

Replaced the sole sorry in `Sheaf.CategoryTheory.DegreewiseFilteredStableQuotient`
with a complete Lean reduction. The existing theorem signature and docstring are unchanged.
The proof constructs the cohomology image filtration, transports it through each supplied
cohomology isomorphism, proves its finite bounds, establishes eventual stationary outer
bounds, proves the boundary inclusion from d²=0, and transports graded pieces using a
commuting square and `cokernel.mapIso`.

Added `Sheaf.CategoryTheory.FilteredCohomologyImage`: a real construction
`CategoryTheory.DecreasingFiltration.cohomologyImage`, with its antitonicity proved by
factorization of homology maps, and the sorry-free theorem
`CategoryTheory.DecreasingFiltration.cohomologyImage_isFinite`. Its lower bound is the
minimum of the three adjacent-degree lower bounds. A short-complex isomorphism gives the
cohomology isomorphism at that bound. Its upper bound uses a monic zero inclusion in degree n,
then zero cohomology of the filtered subcomplex in degree n. No data are chosen from an
unproved existence theorem.

Added `Sheaf.CategoryTheory.FilteredStableSubquotient`, which states only the remaining
local stationary quotient isomorphism. It takes two explicit degreewise outer bounds and
an already proved boundary inclusion. It asserts neither finiteness, existence of a
filtration, transport to an arbitrary abutment, nor eventual stabilization. This is strictly
a part of the original argument.

All new proof imports are non-public. The original public imports are retained for the
unchanged statement. The unused proof import of `Sheaf.CategoryTheory.Filtration` is removed.
A declaration-local `linter.unusedVariables` option preserves the existing named proof
binders ht and hr in the theorem statement while compiling without warnings.

Validation: all three sandbox modules compile in dependency order with lcompile.py.
The import-direction check permits the source-library subobject helper import.
Edge-case review: zero complexes give zero quotients; shifted finite filtrations require
no fixed zero bound; unbounded complexes with bounds varying in n are covered because
only three degrees enter the finiteness proof and only two enter stabilization. At r=1
with the two outer bounds, the remaining comparison has the usual graded homology
presentation. No global finiteness hypothesis was added.

## Proved and sorry left

Closed the item hole in `CategoryTheory.degreewiseFiltered_stable_quotient`
(node `lem-sp-degreewise-filtered-stable-quotient`). Its body now contains no sorry.
This is a decomposition, not a complete axiom-free proof of the original result.

Proved without sorry: `CategoryTheory.DecreasingFiltration.cohomologyImage_isFinite`
(node `lem-sp-filtered-cohomology-image-finite`), the antitonicity proof in the actual
cohomologyImage construction, and the private helpers `gradedPiece_quotient_iso`,
`stableBoundaries_le_cycles`, and `complexStep_antitone`.

Added one hole, and the only sorry in this delivery:
`CategoryTheory.DecreasingFiltration.stableSubquotient_at_bounds`
(node `lem-sp-filtered-stable-subquotient-at-bounds`). It is a public theorem in its own
module with a complete source-based proof in its docstring, and its body is exactly
`:= by sorry`. It compares the two subquotient presentations from Stacks 012Q after
substituting the explicit stationary outer bounds.

Holes closed: 1. Holes added: 1. Net hole reduction: 0. The remaining hole is strictly
smaller: construction, finiteness, eventual bounds, boundary inclusion and transport have
all been discharged in Lean.

## No longer needed

Removed the redundant non-public import `Sheaf.CategoryTheory.Filtration` from the item.
The module remains a statement dependency, through FilteredComplexSubquotients; its
node `def-sp-filtration` is still needed and is not pruned from the closure.

No original DAG node or substantive dependency module is pruned: the original route had
only the two definition nodes `def-sp-filtration` and
`def-sp-filtered-complex-subquotients`, and both are used. No spectral-sequence, bounded
page-core, associated spectral-sequence, ZB-description, first-page, or quotient-complex
image-comparison module is imported by this proof. Their stronger/global hypotheses and
spectral-sequence outputs are unnecessary for this degreewise local argument; they were
search candidates, not original proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The original proof_deps list contains definitions only; there was no declared theorem for
its abelian stationary subquotient calculation. That step is now isolated with explicit
local hypotheses, while the surrounding construction and glue are actually proved.

The original citation of 0132 is contextual (double complexes); the local filtered-complex
calculation is in 012Q and the degreewise finite argument in 012W. The exact definition of
the cohomology image filtration is 012P. The cited local literature files are absent on this
machine, so the Stacks pages 012P, 012Q, 012W and 0132 were read directly online. The source
formula at 012W informally writes the upper tail in degree n in one sentence; the relevant
cycle bound is in degree n+1, as correctly used in the existing node and this Lean proof.

The unit record `sk-prop-av-pqf-finite` has empty realized lists for this imported auxiliary
node. No unit statement, route or record has been changed. No existing statement,
definition, visibility or target signature is changed, and no forced adaptation is needed.

## New nodes

`lem-sp-filtered-cohomology-image-finite`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-cohomology-image-finite.json`, records the
constructed image filtration and its completely proved finiteness theorem. Its module is
`Sheaf.CategoryTheory.FilteredCohomologyImage`. Sources: Stacks 012P and 012W(2).

`lem-sp-filtered-stable-subquotient-at-bounds`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-stable-subquotient-at-bounds.json`, records
the sole remaining local quotient isomorphism in
`Sheaf.CategoryTheory.FilteredStableSubquotient`. Sources: Stacks 012Q final calculation
and the stationary-tail substitutions of 012W. The docstring and node proof spell out the
modular subobject identity and the common quotient presentation. Searches for existing
blueprint nodes and declarations found no exact duplicate with these local hypotheses.

The item node's proof, proof_deps and proof_origin have been updated to match the Lean
reduction. There are no interface change records because no existing public interface
changed.

## Second reading by P1

1. Compared the delivered item module with the repository version. The existing theorem
   signature and all existing declarations are byte-for-byte unchanged; only proof imports,
   private helpers, and the proof body differ. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; there are no errors,
   forbidden declarations, or unlisted `sorry`s. The sole remaining `sorry` is the named
   split theorem `stableSubquotient_at_bounds`, and its node and docstring are present.
   Verdict: pass.
3. Checked the split theorem against the local stationary quotient calculation and searched
   the project/Mathlib search records for duplicates. Its hypotheses are explicit outer bounds
   plus the needed boundary inclusion, so it is strictly smaller than the item and has no
   redundant global finiteness assumptions. Verdict: pass.
4. Checked the proof route from the top downward: Mathlib image, homology, and cokernel APIs
   discharge the construction, finiteness, boundary inclusion, and transport; only the local
   stationary comparison remains split. The removed Filtration import is unused, and the
   retained definition dependencies are used. Verdict: pass.
5. Compared the item node proof, proof dependencies, and proof origin with the Lean proof;
   the two new nodes contain matching declarations, statements, sources, and proof steps.
   The unit's realized route is unchanged. Verdict: pass.

Changed only the report and the delivered proof/modules/node records; no existing interface,
definition, target statement, or unit record was changed.
