## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_perfectLowestCohomologyLocus`
with a complete Lean assembly of the rank-bound open, the closed matrix locus on that
open, and the cohomology pullback comparison. Its signature and public imports are
unchanged. No definitions, existing intermediate statements, or other held modules changed.

Added three modules and their nodes. `PerfectLowestRankBoundOpen` is proved from existing
library declarations: perfect implies pseudo-coherent, the jump-loci theorem, composition
of derived pullbacks, the finite-free field rank calculation, and constructible sets being
retrocompact. Private proved helpers extract the field rank without a finiteness assumption
on global sections and check quasi-compactness separately on every affine target open.
This avoids imposing global quasi-separatedness on the base scheme. Tor amplitude is not
needed for this open reduction and is absent from its signature.

`PerfectLowestMatrixClosedLocus` isolates the closed matrix construction and its
single-pullback criterion under the lowest fibre-rank bound. It asserts neither the
universal criterion nor a cohomology comparison. `PerfectUniversalLowestCohomologyPullback`
isolates the comparison for any map having universally free lowest cohomology; it constructs
no scheme or immersion. Both are strictly separate parts of Tag 0BDL's argument.

The parent proof composes the two immersions and infers immersion, local finite
presentation, and quasi-compactness from Mathlib's composition instances. Its forward
factorization direction applies the single-pullback criterion again after every further
map. Its reverse direction specializes universal freeness to the identity before lifting
through the closed locus. Freeness on the locus is another identity specialization.
The resulting universal condition then supplies the final pullback isomorphisms.

All four modules compiled together through `lcompile.py --all` without warnings.
The official `deliver3.py Y2 Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus
--no-push` dry run passed: commit `668397e5ce` compiled and passed preflight except
for the expected second-reading entry. Nothing was pushed. Temporary profiling options
and scratch Lean files were removed.
The blueprint unit has no realized node identifying this item with a prescribed internal
proof step; the theorem-of-cube route through the original locus statement is retained.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_perfectLowestCohomologyLocus`
(node `lem-sc-perfect-h0-locally-closed`). No sorry remains in the item's module.

The new `AlgebraicGeometry.Scheme.exists_perfectLowestRankBoundOpen`
(node `lem-sc-perfect-lowest-rank-bound-open`) also has a complete proof, with no new hole.
Its existing dependency theorems may still use sorry, as permitted in stage 3.

Added exactly two holes, each the entire proof of a named theorem in its own module:

- `AlgebraicGeometry.Scheme.exists_perfectLowestMatrixClosedLocus`
  (node `lem-sc-perfect-lowest-matrix-closed-locus`).
- `AlgebraicGeometry.Scheme.perfectUniversalLowestCohomology_pullback`
  (node `lem-sc-perfect-universal-lowest-cohomology-pullback`).

This is a decomposition: one existing hole closed and two lower holes added, not a fully
sorry-free proof of Tag 0BDL. Both new holes have the source, a complete proof in words,
and their dependencies recorded in their docstrings and nodes.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`
and `Sheaf.AlgebraicGeometry.PerfectJumpLoci` from the item's module, replacing them with
the three modules used by its Lean proof. These original modules remain needed within the
new intermediate argument, so no global pruning of either is claimed.

The parent's direct proof dependencies are now the three new nodes. Its former dependencies
`lem-sc-perfect-jump-loci`, `def-pc-perfect-complex`,
`lem-sc-perfect-finite-free-residue-model`, and
`lem-sc-square-injective-free-map-dual-coker-zero` are no longer direct steps of the
parent proof; all remain needed below the new nodes or in its statement. No node or module
is proved unnecessary throughout the targets' import closure. No public imports removed.

## Where the brief, the DAG or earlier work was wrong

The supplied dependency interfaces do not state the scheme-level closed matrix construction,
its gluing, or the universally free lowest-cohomology comparison. The new statements expose
these gaps; there is no assertion that the old dependency declarations alone directly imply
the complete locus theorem. The rank-bound reduction, however, could be proved directly.

The local Stacks text is absent on this machine. Read the primary source at
https://stacks.math.columbia.edu/tag/0BDL, especially its rank-bound reduction, its stronger
single-pullback criterion after that reduction, and its matrix-chart comparison. This agrees
with the original statement and explains the stronger single-test criterion of the closed
intermediate theorem. No disputed statement or forced adaptation was found.

Edge cases checked mathematically: on the empty scheme the universal tests and factorization
criterion hold vacuously, and closed construction/gluing uses no chosen point; for rank zero
the first term is zero and its matrix ideal is the zero ideal; if the amplitude interval is
empty, only rank zero can occur on nonempty tests. Nonreduced schemes require the full matrix
ideal rather than its radical. An injective equal-rank free map need not be surjective
(for example multiplication by 2 on the integers), so both remaining proofs explicitly use
zero dual of its cokernel, not splitting. The smaller-rank charts use the strong rank
condition for free modules over nonzero commutative rings, not injectivity after tensoring
with a residue field.

The new-node searches were run through `msearch.py` and are in `searches.jsonl`.
LeanSearch was unavailable (HTTP Internal Server Error); LeanFinder returned related field,
free-locus, ideal-sheaf and pullback declarations but no result stating these intermediate
scheme-level assertions. The recorded Mathlib grep searches had no exact match. Blueprint
searches for lowest cohomology, fibre rank, matrix and cohomology pullback found no equivalent
blueprint statements; the ancestors are the original theorem-of-cube construction clause.

## New nodes

`lem-sc-perfect-lowest-rank-bound-open`, in `PerfectLowestRankBoundOpen`, is the proved
rank-bound open reduction, valid without a Tor-amplitude hypothesis. Its statement retains
both the exact Betti sublevel and the factorization of universally free test maps.

`lem-sc-perfect-lowest-matrix-closed-locus`, in `PerfectLowestMatrixClosedLocus`, is the
closed construction on a rank-bounded open, with a single-pullback criterion. Its proof
records the finite matrix ideal, converse through the zero-dual lemma, smaller-rank charts,
and gluing of the uniquely characterized closed subschemes.

`lem-sc-perfect-universal-lowest-cohomology-pullback`, in
`PerfectUniversalLowestCohomologyPullback`, is only the arbitrary-pullback comparison under
universal freeness. Its proof records residue models, the vanishing matrix argument, and
gluing of canonical local comparisons. No change record is needed: no existing signature,
definition, or public import was changed.

## Second reading by Y2

1. **No accidental visible changes.** Compared the delivered parent module with the repository version: the theorem signature and all existing declarations are byte-for-byte unchanged. The three added modules introduce only the declarations and nodes listed in this report; no target statement or definition was changed. Verdict: pass.

2. **Proof and compilation.** Compiled all four modules with `lcompile.py --all`; they compile without errors or warnings. The parent theorem has no `sorry`; the only remaining `sorry`s are the two explicitly named split-off theorems, each public and documented with a proof plan and matching node. No forbidden declaration or hollow definition occurs. Verdict: pass subject to the two recorded split-off holes.

3. **Statements and new nodes.** Checked the signatures against their node JSON and checked the rank-bound edge cases (empty scheme, rank zero, and empty amplitude interval). The rank-bound result is a direct open sublevel statement; the matrix result is only the single-pullback closed criterion; the pullback result asserts only the comparison isomorphism. They are strictly smaller than the parent target and do not duplicate it. Searches recorded in `searches.jsonl` found no existing equivalent declaration. Verdict: pass.

4. **Downward route and pruning.** The parent proof follows the rank-bound open, matrix closed locus, and universal pullback route. Public imports are limited to statement dependencies; proof-only dependencies are plain imports. The removed direct dependencies remain below the new nodes, so no additional global pruning is claimed. Verdict: pass.

5. **DAG and unit agreement.** The parent node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof, and each new node has matching module, declaration, statement, source, proof steps, and provenance. The unit has no prescribed realized internal node for this item, so the theorem-of-cube route remains valid. Verdict: pass.

I changed only this second-reading report section; no Lean source, node, or import required repair.
