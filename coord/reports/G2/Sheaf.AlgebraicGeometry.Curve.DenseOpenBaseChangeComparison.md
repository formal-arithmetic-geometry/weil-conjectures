## What changed

Proved `AlgebraicGeometry.IsCurve.dense_open_baseChange_comparison` with its statement
unchanged. The only delivered Lean module is
`Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison`. The returned duplicate
private square helper is removed. The isomorphism square now applies the existing
`AlgebraicGeometry.IsCurve.bijective_square_iff` theorem via a proof-only
`import all Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange`, which exposes the
existing private declaration to this proof without changing its original module.

The proof reuses the existing private `IsCurve.dense_open_all_base_change` from that
module, which combines the existing low-degree and higher-degree comparisons. The
duplicate `module_dense_open_all_base_change` has also been removed in second reading. A complete private coefficient-isomorphism proof identifies
changing coefficients after abelian extension by zero with module extension by zero;
it restricts the coefficient adjunction to sheaf categories and uses uniqueness of left
adjoints. The existing all-degree equivalence and a commuting square transport comparison
bijectivity along this isomorphism.

The counit monomorphism passes invertible-order and primary torsion to G. In the primary
case, an additional invertible-order hypothesis forces every stalk element to be zero
by coprime annihilators; stalk conservativity and cohomology of zero finish C6.
Proper comparison uses the all-degree equivalence in both directions. No constructibility
hypothesis is needed by this proof, and the reverse proper implication does not need the
stated torsion alternative; both hypotheses remain in the statement.

Added proof-only imports:
- `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange`
- `Mathlib.CategoryTheory.Adjunction.Restrict`
- `Mathlib.CategoryTheory.Adjunction.Whiskering`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `WeilConjectures.CategoryTheory.Sites.Point.Linear`

Updated the item's node proof, proof dependencies, and proof origin to describe this
route. All public imports and all public declaration signatures are unchanged.
The unit `sk-thm-p1` route through dense-open reduction is retained.

Validation: a scratch `import all` check resolves the existing private square theorem
from the unchanged compiled library. The repaired item compiles locally with no errors
or warnings. `tools/import_prune_check.py` passes against the repository original.
The required `deliver3.py --no-push` dry run printed OK: local compilation, the axiom
probe, server compilation and preflight pass except for the designated second reading.
Nothing was pushed.

## Proved and sorry left

`AlgebraicGeometry.IsCurve.dense_open_baseChange_comparison`: complete proof written;
1 of 1 original sorries replaced. No sorry remains in the delivered Lean module, and no
new modules or sorry declarations are added. The square theorem was already proved
and reusing it is not counted as closing another hole. Existing comparison dependencies remain
separate stage-3 items; this delivery does not assert that their proofs are finished.

## No longer needed

The duplicate `AlgebraicGeometry.bijective_square_iff` helper is removed. Its proof is
reused from `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange` instead.

All six original public imports describe the unchanged public statement and remain.
The following original proof-only imports were removed (their required declarations
are available through the retained/new interfaces):
- `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`
- `Sheaf.AlgebraicGeometry.CurveCoefficientPair`
- `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`
- `Sheaf.Paper.ZeroDimensionalCohomology`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.Finite.Stalk`
The existing all-degree comparison is reused from `DenseOpenBaseChange`, which
itself imports `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology`. Thus
`lem-pbc-s2-dense-open-cohomology-pullback` (module
`Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyPullback`) is now transitively
reachable. Its additional comparison is not used by this proof, but this repair makes
no claim that the module is pruned from the import closure.

The following former direct proof dependencies are replaced by the existing
all-degree comparison interface:
- `lem-weil-pbc-cohomology-pullback-derived-unit`
  (`Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`)
- `lem-weil-pbc-five-lemma` (Mathlib five-lemma statements)
- `lem-weil-pbc-pullback-cohomology-long-exact-ladder`
  (`Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`)
- `lem-weil-pbc-zero-dimensional-cohomology`
  (`Sheaf.Paper.ZeroDimensionalCohomology`)
- `lem-weil-pbc-zero-dimensional-field-extension`
  (`WeilConjectures.AlgebraicGeometry.Curve.Reductions`)
- `lemma-weil-pbc-finite-direct-image-exact`
  (`WeilConjectures.SixFunctors.Finite.Exact`)
- `lemma-weil-pbc-finite-stalk-formula`
  (`WeilConjectures.SixFunctors.Finite.Stalk`).

These are no longer used directly by this module; some remain dependencies of the
comparison lemmas, so this is not a claim that all are globally unreachable.
The following definition nodes also leave the direct proof list, while definitions
needed by the statement remain in `stmt_deps`:
`def-weil-geometric-point`, `def-weil-pbc-cohomology-pullback`,
`def-weil-pbc-constructible-torsion`, `def-weil-pbc-curve-setting`,
`def-weil-pbc-direct-image`, `def-weil-pbc-etale-cohomology`,
`def-weil-pbc-extension-pullback`, `def-weil-pbc-geometric-stalks`,
`def-weil-scheme-morphism-properties`.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified a word-for-word duplicate of an existing private
helper. Repair: remove the duplicate, use proof-only `import all` on the original module,
and qualify both calls as `IsCurve.bijective_square_iff`. No hypotheses,
conclusions or proof of the existing helper change. The earlier second reading predates
this repair and has been removed so the designated second reader reviews the new set.

The original node's one large proof step did not account explicitly for the coefficient
transport: G is coefficient change of abelian extension by zero, whereas the existing
comparison interfaces use module extension by zero. This transport is now proved,
without adding a new obligation. The original plan's geometry is otherwise retained
through the reused all-degree interface and its low- and high-degree ingredients.

The literature checkout is absent on this machine. Read Stacks Tag 0GJA directly at
https://stacks.math.columbia.edu/tag/0GJA, especially its exact sequence, higher-degree
isomorphisms, and remarks (a),(c). The coefficient-isomorphism proof is formal category
theory, using the existing restriction and extension-by-zero adjunctions.

Searches: launcher LeanFinder returned unrelated etale algebra and scheme-section results;
Loogle returned generic bijectivity lemmas; launcher grep found no coefficient-transport
comparison; LeanSearch returned HTTP 500 (unavailable, no mathematical verdict).
Direct rg and signature reading located the three existing comparison interfaces and
Mathlib's `Adjunction.restrictFullyFaithful` and `Adjunction.leftAdjointUniq`.

At the start of validation the source files for the recently landed low-degree and
pulled-counit interfaces were present but their oleans were absent from the compiled
cache. This was handled by waiting for publication, without recompiling or restating
the dependencies; their compiled files then appeared and full compilation passed. Scratch placeholders used while checking independent glue are outside
`lean/` and are not delivered.



## Second reading by G2

1. Compared the delivered module against the repository original. The existing public
   theorem signature is byte-for-byte identical; its docstring and all six public imports
   are unchanged. No definitions, targets, or other modules change. Verdict: pass.
2. Compiled the repaired module locally without errors or warnings. Searched for forbidden
   constructs and sorry: none occur in the delivered source. A fresh scratch copy prints
   axioms for every local helper and the target: the helpers use only propext,
   Classical.choice, Quot.sound; the target also uses sorryAx through existing imported
   obligations (including DenseOpenClosedTerm), which remain open and are not newly added.
   The coefficient adjunction directions, counit monomorphism, coprime annihilators, and
   comparison-square orientations were read explicitly. Verdict: pass as a reduction
   closing the item's own hole, not a completed transitive proof.
3. No statements are split off, no new sorry is added, and no new node is delivered.
   Searched the library for coefficient isomorphisms, left-adjoint uniqueness, primary
   torsion, and all-degree dense-open comparisons. Found the existing private
   IsCurve.dense_open_all_base_change, with the same generality as the duplicate helper.
   Reused it. The coefficient isomorphism needs no cohomological hypothesis; the identity
   open and empty open behave correctly. The primary/invertible-order case gives zero
   stalks even at exponent zero; characteristic zero has no primary branch with prime p.
   Verdict: pass; duplication repaired.
4. Read the reused all-degree proof and its low/high interfaces, the C6/C7 definitions,
   Stacks Tag 0GJA, and sk-thm-p1's realized route. Dense-open reduction remains in that
   route. Removed the duplicate helper and its three proof-only imports; no public import
   was added or removed. The original dependencies no longer directly used are all listed
   above. No claim of global pruning is made: DenseOpenBaseChange retains their transitive
   imports, including DenseOpenHighCohomologyPullback. Verdict: pass after shortening.
5. Checked the delivered node diff: only proof, proof_deps, and proof_origin change;
   statement and stmt_deps are untouched. Updated step 2 to cite
   lem-pbc-s2-dense-open-base-change for its reused private all-degree proof, and recomputed
   proof_deps as the union of the steps' uses. No unit record changes. Verdict: pass.

Second reading changed: removed the duplicate module_dense_open_all_base_change, called
IsCurve.dense_open_all_base_change directly, removed the three now-unneeded direct imports
DenseOpenLowBaseChange, DenseOpenHighCohomologyHigh, and DenseOpenPulledCounitHigh, and
updated the node and report. These modules remain transitively imported. Holes closed:
AlgebraicGeometry.IsCurve.dense_open_baseChange_comparison (one). Holes added: none.
