## What changed

Proved `Algebra.finite_completion_factor_idempotent` in
`Sheaf.RingTheory.FiniteCompletionFactorIdempotent`, with its signature and existing docstring
unchanged. The proof follows all three steps of the node: clearing away denominators gives the
local-ring equivalence; coordinate comparison identifies the chosen completion factor map;
supported tuples supply the idempotent, partial inverse, surjectivity and kernel annihilation.

Added the proof-only import `Sheaf.RingTheory.PairHenselizationCompletionData`. Its existing
`RingTheory.pair_henselization_completion_data` provides the completion equivalence with the
necessary coordinate formula. Two proved private helpers handle ideal transport and the abstract
supported-tuple calculation. No new public declarations, definitions, or statements were added.
A declaration-local heartbeat allowance accommodates the completion and tensor instance
calculations. Updated the item's node proof and dependencies to record the actual route.

## Proved and sorry left

Closed the one original hole: `Algebra.finite_completion_factor_idempotent`
(node `lem-weil-pbc-finite-completion-factor-idempotent`). Both private helpers
`Algebra.completion_equiv_of_ringEquiv` and `Algebra.factor_idempotent` are proved.
There are no `sorry`s left in the delivered module and no holes added or split off.

This proves the item from existing named dependencies, principally
`AdicCompletion.completion_finite_extension_decomposition` and
`RingTheory.pair_henselization_completion_data`; it does not claim to close the remaining
holes in the former's transitive dependencies.

## No longer needed

None. The existing proof dependency import is used, all three planned steps are implemented,
and no planned node or module was bypassed. The unit's realized route is preserved.
The new completion-comparison import is used by the private completion-equivalence helper.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The previously stated plan's componentwise completion
construction is already available as `RingTheory.pair_henselization_completion_data`;
the updated node records this existing dependency explicitly. No interface corrections or
forced adaptations were necessary.

## Second reading by V3

1. **Interface: pass.** Diffed the sole delivered module against the repository. The
   existing theorem signature is byte-for-byte identical, its docstring is unchanged,
   and no existing definition or public visibility changed. The only new import is
   proof-only. The two added helpers are private proved theorems; the heartbeat option
   applies only to this theorem. No statement change or change record is needed.
2. **Proof: pass.** Independently compiled the module locally with `lcompile.py`, without
   errors or warnings (36.1 seconds). Scanned the source for forbidden declarations and
   holes: none. Compiled a scratch copy with `#print axioms` for both private helpers and
   `Algebra.finite_completion_factor_idempotent` (36.5 seconds). Both helpers use only
   `propext`, `Classical.choice`, and `Quot.sound`; the item additionally uses `sorryAx`
   through the existing finite-completion decomposition's open dependencies. This closes
   the item's named hole, not its transitive dependency closure. Supported tuples and
   inverses are constructed explicitly within the proof; no definition chooses arbitrary
   data from an unproved mere-existence statement.
3. **Split statements: pass, none added.** There are no split-off statements or new nodes.
   Read the private helpers and their applications: quotient equivalences supply the
   coordinate comparison, and the supported-tuple argument proves all five requested
   conjuncts. The latter works for a singleton index set, arbitrary complementary factors,
   and trivial factor rings; the selected index rules out an empty entire index set.
   Ideal transport also handles zero and unit ideals. No extra hypotheses are hidden.
4. **Route and pruning: pass.** Read both imported Sheaf statements and proofs and the
   unit `sk-thm-p1`'s `realized` record. All three original node steps are implemented;
   no realized unit step is bypassed. No old proof dependency is dropped, so `No longer
   needed: None` is complete. Every explicit import supports the interface or proof.
   Independent Lean Finder search for completion transport, Loogle search for supported
   tuples, and `rg` searches of Mathlib and both library roots found no shorter replacement
   for the full argument. `AdicCompletion.congr` is a linear equivalence over a fixed
   scalar ring. The existing `AdicCompletion.exists_ringEquiv` supplies only compatibility
   on the original ring, whereas this proof needs compatibility at every quotient
   coordinate; the chosen `pair_henselization_completion_data` supplies exactly that.
5. **Nodes: pass.** Compared the delivered node with the repository: only `proof`,
   `proof_deps`, and `proof_origin` differ. The dependency list equals the union of step
   `uses`; the added completion-comparison dependency matches the actual private helper.
   The statement, Lean signature record, source, unit, and blueprint attachment are
   unchanged. There are no new nodes requiring additional fields.

Second reading changed only this report, adding the independent checks and explicitly
recording the remaining transitive `sorryAx`. No Lean or node repair was necessary.
