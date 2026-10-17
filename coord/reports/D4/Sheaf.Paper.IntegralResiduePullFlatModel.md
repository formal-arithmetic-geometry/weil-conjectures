## What changed

The flatness conjunct of `residueExchangePull_flatModel` is proved from pullback flatness,
colimit K-flatness, and the derived counit theorem. The unresolved comparison equality is
isolated in the new module `Sheaf.Paper.IntegralResiduePullFlatModelComparison` and imported
privately.

## Proved and sorry left

Proved: the flatness conjunct of
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_flatModel`.
One sorry remains in
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_flatModel_comparison`,
node `new-integral-residue-pull-flat-model-comparison`. No other holes were added.

## No longer needed

The proof-only import `Sheaf.Paper.IntegralResiduePullOrdinaryUnit` and the proof-only
import `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` were removed.
The former was only used by the discarded direct mate attempt; the latter and the private
helper section implementing that attempt are no longer reachable after the comparison is
split into its own theorem. The square-data and pullback-flatness imports remain used.

## Where the brief, the DAG or earlier work was wrong

The earlier complete proof attempt reaches a deterministic 400000-heartbeat timeout while
elaborating the final mate specialization. The obstruction is the composed homotopy-category
object conversion between `(R ⋙ U).mapHomotopyCategory` and the corresponding composition of
`mapHomotopyCategory` functors. The flatness part and restriction/pullback factorization
compile independently, so the unresolved equality is a strictly smaller named statement.

## New nodes

`new-integral-residue-pull-flat-model-comparison` records the second conjunct as a strictly
simpler theorem with its source and derived-mate proof plan. It is stated in
`lean/Sheaf/Paper/IntegralResiduePullFlatModelComparison.lean`; its proof remains `sorry` for
the next worker. The interface/pruning change record is
`coord/changes/integral-residue-pull-flat-model-interface.md`.

## Second reading by D4

1. **Signatures and accidental changes.** I diffed both delivered modules against the
repository versions. The existing declaration `residueExchangePull_flatModel` has the
identical signature; only its proof, proof-only imports, and private implementation text
changed. The new comparison declaration is recorded verbatim in its new DAG node. No
change record is needed. Verdict: pass.

2. **Compilation and axioms.** I compiled the comparison module and the main module with
`lcompile.py`; both compile without errors or warnings. The comparison theorem is the one
named sorry listed in the report, and the target theorem depends on its `sorryAx` as expected.
There are no definitions containing sorry, axioms, unsafe/opaque/extern declarations, or
other forbidden constructs. Verdict: pass.

3. **Truth and strength of split statements.** The remaining split theorem is exactly the
second conjunct of the target, with the same hypotheses and displayed maps, and has a
docstring proof plan citing Bhatt--Scholze Remark 6.8.15. It is strictly smaller than the
conjunction and introduces no weakened target statement or hollow definition. Verdict: pass.

4. **Shortest route and pruning.** The flatness conjunct now uses the proved pullback-flatness
lemma, colimit K-flatness, and the derived counit theorem directly. The unresolved mate
calculation is delegated to the named comparison theorem. I removed the unused private mate
calculation section (cached instances, square/mate helpers, and factorization lemmas), the
unused ordinary-unit import, the unused derived-mate import, and stale heartbeat/backward
definition options. Verdict: pass.

5. **DAG and unit route.** The main node's proof steps and `proof_deps` now match the Lean
proof, including `new-integral-residue-pull-flat-model-comparison`. The new node has the
required source, proof plan, searches, Lean record, chapter, and unit. The unit
`sk-thm-properbasechange` record is unchanged and its realized route is preserved. Verdict:
pass.

Changed in this second reading: pruned the dead direct-mate implementation and its two
proof-only imports, removed stale proof options, and updated this report. The only hole left
is `residueExchangePull_flatModel_comparison`; no new hole was added.
