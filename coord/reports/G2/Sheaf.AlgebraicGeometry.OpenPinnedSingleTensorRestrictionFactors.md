## What changed

Completed `AlgebraicGeometry.open_pinned_single_tensor_restriction_factors` in
`Sheaf.AlgebraicGeometry.OpenPinnedSingleTensorRestrictionFactors`, preserving its
statement, universes, visibility, and imports. Four proved private helpers implement
exact single comparison, the degreewise composition square, its homotopy quotient,
and the derived square. The proof follows the existing node's plan: cancel the
quotient comparison factors, check degree zero and the zero terms, apply the
homotopy quotient and Qh, and use naturality of exact restriction.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.open_pinned_single_tensor_restriction_factors`
(node `lem-pc-open-pinned-single-tensor-restriction-factors`). Both conjuncts are
proved. No holes remain in the item and no holes were added or split off. All four
private helpers have complete proofs. This is a proof, not a decomposition.

## No longer needed

None. The existing public import of
`Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso` remains necessary for
the statement's constructed comparison isomorphisms. Both existing proof dependency
nodes remain used: `def-pc-open-pinned-single-tensor-restriction-iso` and
`def-pc-derived-open-restriction-maps`. No new proof imports are needed. The saved
copy of the dependency module was removed from the sandbox delivery.

## Where the brief, the DAG or earlier work was wrong

The preceding attempt was blocked by a missing published olean. That dependency is
now present in the published build; recompiling its source as part of this delivery
is unnecessary. The DAG's mathematical plan works without changes to any
statement or definition. Category aliases require explicit source and target
categories when specializing the general comparison calculation, and local
restriction additivity instances, as in the existing homotopy comparison definition.

## Second reading by G2

1. **Visible declarations — pass.** Diffed the only delivered module against the
   repository. The existing theorem signature is byte-for-byte identical, including
   universes, hypotheses, let-bound comparisons and both conclusions. The header,
   public import, visibility and existing docstring are unchanged. There are no
   definition changes or change records; only four private proved helpers and the
   original theorem's proof were added.
2. **Proof checking — pass.** Compiled the module with `lcompile.py` without errors
   or warnings (51.8 seconds). Compiled a scratch copy with `#print axioms` for the
   theorem and all four helpers (49.5 seconds): each uses exactly `propext`,
   `Classical.choice` and `Quot.sound`, with no `sorryAx`. Checked that there are no
   textual holes, forbidden declarations, hollow definitions or overlong lines.
3. **Split statements — pass, none.** No statements were split off and no new
   public declarations or nodes were introduced. Read all four private helper
   statements and their proofs. The complex square reduces in degree zero to
   identity composition with the component of the given isomorphism; away from
   zero, zero-object maps agree. This also covers zero modules, identity functors
   and empty opens without extra assumptions. No arbitrary data are chosen by
   the delivered proof.
4. **Route and pruning — pass.** Followed the proof from the two conjuncts through
   exact-single comparison, naturality, the homotopy quotient and the degreewise
   square. Fresh Loogle and LeanFinder searches for homotopy factorization and
   single-comparison compatibility found the constituent APIs already used.
   Read Mathlib ExactFunctor and searched the library. The similar private square
   in `RestrictedDerivedSectionsSingle` requires every functor to be exact and
   cannot replace this calculation for additive tensor pullbacks. The sole public
   import supplies the comparison definitions in the existing signature and is
   necessary. Both old proof dependencies remain used, so `No longer needed` is
   complete. Read `sk-thm-picard-f-representable.json`: its realized entries are
   empty and unchanged; this termwise tool calculation bypasses no realized unit
   statement or step.
5. **DAG agreement — pass.** Read
   `lem-pc-open-pinned-single-tensor-restriction-factors.json` and its two dependency
   constructions. The existing proof plan describes exactly the calculation now
   implemented: cancel quotient comparisons, use restriction-factor naturality,
   check the single square termwise, and apply quotient and Qh. Its `proof_deps`
   and `proof_origin` remain accurate. No new node fields are needed.

Changes in this reading: this review report only; the Lean proof and DAG needed
no repair. One original hole was closed, none added, none split off; no imports
or modules were pruned.
