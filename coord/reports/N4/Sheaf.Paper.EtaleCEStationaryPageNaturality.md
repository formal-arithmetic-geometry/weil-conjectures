## What changed

Replaced the stationary-page naturality hole by a proof from a local stationary-cycle
comparison. Constructed CE degreewise bounds, transported homology-image epimorphisms,
and induced step maps by image factorization. Naturality is proved by applying the
representative hypothesis to actual cycles and cancelling epimorphic projections.
All existing declaration signatures and public imports are preserved. Completed
the earlier unfinished assembly: typed the family of step maps explicitly, proved
compatibility by monomorphism cancellation, and transported the naturality square
along q+(n-q)=n using a proved private categorical helper. The held module has
no remaining sorry. Both delivery modules compile through lcompile.py; the
deliver3.py --no-push check passes. Nothing was pushed.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.exists_etaleCE_stationary_page_comparisons` (node
`lem-weil-pbc-ce-stationary-page-naturality`) by decomposition, not a completed
axiom-free proof. Added one hole:
`CategoryTheory.filteredStationary_cycle_comparison`, node
`lem-weil-pbc-stationary-cycle-comparison`. No other holes are added or left in the item.
The new obligation concerns one filtered complex at one bidegree and page, with no
family choices, spectral-sequence maps, or naturality assertion. Its equations
uniquely determine its witnesses; no arbitrary existence data enter definitions.

## No longer needed

Removed proof import `Sheaf.CategoryTheory.DegreewiseFilteredStableQuotient` and
proof dependency `lem-sp-degreewise-filtered-stable-quotient`. Its bare objectwise
isomorphism does not supply the representative normalization required here.
The new local comparison still uses the stationary subquotient argument, so that
argument and its prerequisites are not claimed pruned. No public imports removed. The remaining planned stationary-subquotient
dependency is imported privately in the new comparison module.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox assembly did not compile and still ended in an anonymous
sorry. Its degree-transport helper, an untyped existential family, shadowed
bounds and an incorrect cokernel lemma name were repaired. The final transport
is now a complete Lean proof. The theorem-scoped unused-variable linter option
accounts for the unchanged existential binder names in its public signature.

The planned stable-quotient declaration provides only `Nonempty` isomorphisms;
it does not specify their action on cycle representatives. Naturality therefore
requires the strictly local normalized comparison now stated separately.
Searches: LeanFinder and Loogle found homology projection naturality; source grep
found the existing objectwise stationary statements but no normalized comparison.
LeanSearch returned Internal Server Error. The Stacks Homology source was read at
its graded-cohomology formula and finite-filtration convergence proof, fetched
into the sandbox scratchpad because the repository lacks the source text.
The existing normalized quotient and graded cohomology presentation theorems
were also inspected: each gives only a Nonempty isomorphism, without its
projection equation. Their types therefore do not replace the new local
comparison. Loogle reconfirmed HomologicalComplex.homologyπ_naturality.
Edge cases checked: zero complexes, zero graded pieces, empty total diagonals,
and r=1 under the two explicit stationary bounds. None requires a stronger bound.

## New nodes

`lem-weil-pbc-stationary-cycle-comparison` in
`lean/Sheaf/CategoryTheory/FilteredStationaryCycleComparison.lean` is the single
remaining local quotient-and-representative obligation. Its source, complete proof
in words, search records and Lean signature are in the matching node and docstring.
No interface change or forced adaptation; no change record is needed.

## Second reading by N4

1. PASS: compared the held module against the repository with diff and checked
   the original theorem signature and both preceding public definitions byte for
   byte. Existing statements, definitions, visibility and public imports are
   unchanged. There are no forced adaptations or interface change records.
2. PASS (decomposition): both delivery modules compile through lcompile.py.
   The held module has zero sorry; the new module has precisely the named hole
   `CategoryTheory.filteredStationary_cycle_comparison`, whose entire proof is
   `by sorry`. No forbidden declarations or hollow definitions occur. Scratch
   `#print axioms` checks of both public theorems report exactly propext,
   Classical.choice, Quot.sound and sorryAx. The delivery probe also checks all
   declarations. One old hole is closed and one new hole added: net zero, not an
   axiom-free proof of the original result.
3. PASS: read the split-off theorem, its node and its complete docstring proof
   against the explicit complexCycles/complexBoundaries definitions and the
   Stacks graded-cohomology formula. Writing A=F^q K^n, A'=F^(q+1) K^n,
   Z=ker d and B=im d, both quotients are (A intersection Z) modulo
   (A intersection B)+(A' intersection Z). The upper/lower bounds replace the
   outer steps by zero/top without requiring bounds in other degrees. Zero
   complexes and A=A' give zero quotients; with zero differentials they give
   A/A'; r=1 gives the same calculation when its explicit bounds hold.
   The cycle-inclusion equation fixes z by monicity, and its epic composite
   with page projection fixes the comparison. No arbitrary witness enters a
   definition. This single-complex comparison omits the family, boundedness
   construction, image-map construction and naturality of the original item,
   so it is strictly a part of the argument, not a restatement. Independent
   LeanFinder, Loogle and grep searches used different queries, recorded in
   the new node. Read the existing normalized quotient, graded cohomology and
   stable-subquotient presentation proofs: their Nonempty isomorphism
   conclusions do not specify a projection equation, so they cannot replace
   the normalized comparison by direct application. Completing its generic
   abelian kernel/image identification requires more than a short repair.
4. PASS: read the proof from its conclusion down through degree transport,
   epi cancellation on representatives, restricted homology images and CE
   filtration bounds. Those constructions use actual image factorizations.
   All held-module imports are needed; the original public differential
   import occurs in the signatures. Tested removing the new module's public
   Mathlib homology import: Lean reports its signature constants privately
   imported, so retained it. The sole old proof dependency no longer used is
   `lem-sp-degreewise-filtered-stable-quotient`, and its removed import is
   fully listed above. Its stationary-subquotient prerequisites remain needed
   by the new obligation; no whole-library pruning is claimed. Read
   dag/units/sk-prop-h2.json: its realized lists are already empty, and this
   delivery changes no unit statement, step or realized assignment. The
   replacement stays below the unit level.
5. PASS after repair: both nodes' proof_deps equal the union of their steps'
   uses; their proof/proof_origin records match the reduction and local
   stationary calculation. Existing node changes are confined to the allowed
   proof fields. The new node has source, proof in words, searches, creation
   and blueprint provenance, chapter/unit and Lean record. Replaced its
   single-line normalized Lean signature with the exact multiline source
   signature, and added the missing private FilteredStableSubquotient import
   for its recorded proof plan. Recorded the independent searches in that
   node. No proof bodies or existing signatures were changed in this reading.
