## What changed

Repaired the existing private theorem
`AlgebraicGeometry.ProEtale.CondensedRing.restrict_pull_fac` in
`Sheaf.Paper.IntegralResiduePullFlatModel`. Unfold the explicitly constructed
restriction/pullback square and the typed counits, apply the retained generic
`exactLeftSquareFac`, and normalize inverse/composition isomorphisms. This proves
the exact restriction/pullback factorization against the synchronized source.

Restored the proof infrastructure and the public theorem's source/proof docstring
that the first-reader sandbox had deleted. Relative to the shared source, only
the body of `restrict_pull_fac` changes. Every existing declaration, definition,
visibility, option, attribute and import is retained. The DAG's `proof_origin.note`
now distinguishes this completed helper from the still-open target plan.
The earlier sandbox change record was withdrawn: there is no interface change.

## Proved and sorry left

Holes closed (one):
`AlgebraicGeometry.ProEtale.CondensedRing.restrict_pull_fac` (private).

Holes added: none. No statements were split off.

The single remaining hole is the existing public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_flatModel`, node
`new-integral-residue-pull-flat-model`. Its statement and complete existing
source/proof docstring are preserved. This delivery proves one of the shared
module's two holed declarations; it does not claim to prove the flat-model theorem.

A scratch copy of the delivered source compiled in 15.7 seconds. Its
`#print axioms AlgebraicGeometry.ProEtale.CondensedRing.restrict_pull_fac` reports
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` inherited from open
imported dependencies. The helper itself contains no `sorry`.

## No longer needed

None. No modules, imports or proof dependencies are pruned. The public target is
still open, so its original proof-dependency imports and DAG plan are retained.

## Where the brief, the DAG or earlier work was wrong

The first-reader sandbox deleted every calculation helper, including the holed
restriction/pullback factorization, without proving the public target. It also
deleted that target's required source and natural-language proof docstring.
The report's claimed interface repair did not describe a concrete interface
change. This reading restores the shared declarations and documentation and
repairs the private factorization rather than retiring it.

The final concrete derived-mate specialization remains unresolved. Both the
retained concrete assembly and a fully proved generic assembly reach an expensive
conversion at the final specialization. A 400000-heartbeat check fails there;
a larger allowance exceeds the 60-second file limit. These experiments are kept
only in scratch files. None of their additional declarations, scope changes or
budget changes is delivered. The completed factorization has no such timeout.

## Second reading by C4

1. Compared the delivered module with the shared module using `diff`, and checked
   every existing declaration signature. Verdict: unchanged byte for byte; no
   definition, public import, visibility, instance registration or target meaning
   changes. The original theorem docstring and private helpers are restored.

2. Read the factorization proof and its generic dependencies. The square is the
   inverse of `derivedComapUpperStarIso`, whiskered with the two exact-pullback
   identifications. `exactLeftSquareFac` is applied with integral restriction,
   integral pullback, residue pullback, and source restriction, in that order.
   Its isomorphism is `comapUpperStarIso`; inverse and associativity normalization
   gives exactly the existing statement. The delivered source compiles and the
   explicit scratch axiom check above permits only the three standard axioms and
   inherited `sorryAx`. No new axiom, unsafe declaration, opaque declaration,
   external implementation, definition hole or arbitrary chosen data is added.
   Verdict: the private hole is closed; the public hole is honestly retained.

3. No new public statements, split-off statements, or nodes were introduced.
   Searched the shared Lean sources for localization-factor and derived-mate
   results, and used msearch Loogle and LeanFinder. LeanFinder returned the
   existing derived unit/counit factorization API; Loogle did not index the
   project's composition-factor lemma. The upstream exact-derived-adjunction
   unit theorem requires exact scalar extension and cannot replace the mixed
   unit argument without an extra flatness assumption. Verdict: no duplicate or
   restatement is being delivered. The retained generic factorization uses only
   exactness of restriction and pullback, with no residue-flatness assumption;
   identity functors, zero complexes and empty schemes introduce no exception.

4. Read the original proof-dependency modules and the retained generic
   calculations from the target down. The repaired helper uses the existing
   exact-square reduction and requires no new mathematical lemma. Read
   `dag/units/sk-thm-properbasechange.json`: its three realized steps and unit
   dependencies are unchanged. Since the public proof remains open, no import
   or unit-route pruning is claimed. Verdict: the existing route is preserved.

5. Compared the node and its Lean record with the source. The declaration and
   statement remain identical; `proof` and `proof_deps` still describe the open
   target's plan. Updated only `proof_origin.note` to record the completed
   restriction/pullback factorization and explicitly mark the public target
   as open. Verdict: no metadata falsely claims the public theorem is proved.

Changes made by this reading: restored the deleted helpers and target docstring;
proved `restrict_pull_fac`; removed the inaccurate interface-change record;
rewrote this report and corrected the node's proof-origin note.
