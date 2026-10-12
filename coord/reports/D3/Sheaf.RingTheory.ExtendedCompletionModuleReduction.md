## What changed

Proved `AdicCompletion.extendedCompletion_module_reduction` in
`Sheaf.RingTheory.ExtendedCompletionModuleReduction`, with its signature and visibility
unchanged. Added only the proof import `Mathlib.RingTheory.AdicCompletion.Completeness`.
Updated `lem-weil-pbc-extended-completion-module-reduction` to record the actual route.

The coordinate hypothesis identifies the base ring maps and therefore the two extended
ideals in the completed target. Evaluation at level one has exactly this kernel by
Mathlib's `AdicCompletion.ker_evalOneₐ_eq_map`, applied to the finitely generated ideal
`Ideal.map φ I`. A second coordinate calculation identifies the quotient scalar action.
Finiteness then transports through the evaluation's first isomorphism theorem and from
the completed base to its quotient. All proof dependencies are proved Mathlib declarations.
No new declarations, definitions, statement changes, or change records.

## Proved and sorry left

Closed the sole hole: `AdicCompletion.extendedCompletion_module_reduction`
(node `lem-weil-pbc-extended-completion-module-reduction`). One of one holes proved;
zero holes added or split off. No `sorry` remains in any delivered Lean file.

Local single-file compilation succeeds without errors or warnings. The proof works with
all original hypotheses, including arbitrary commutative rings and a finitely generated
ideal without Noetherian assumptions. The cases `I = ⊥`, `I = ⊤`, and zero rings require
no separate argument: the quotient/evaluation lemmas apply to them unchanged.

## No longer needed

Removed proof dependency `lem-weil-pbc-module-completion-complete`. No separate module
completion comparison, canonical completed-module action, or completeness assertion is
needed: the ring-completion quotient theorem for `J = Ideal.map φ I` suffices. This node
is a Mathlib leaf, so no separate Sheaf module is pruned by this removal.

The proof also does not need to construct the base quotient isomorphism
`AdicCompletion I R / K ≃ R/I`; surjectivity of the base evaluation and enlargement of
scalars suffice. The node `lem-weil-pbc-adic-completion-mod-ideal` stays needed for the
target evaluation's kernel and surjectivity.

No original imports were removed. The attempted explicit proof import
`Mathlib.LinearAlgebra.Isomorphisms` was removed after compilation verified that the
required declaration is already available through the retained imports. No unit-level
statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned comparison of ring and module completions is
unnecessary for this reduction: equality of extended ideals follows directly from the
coordinate condition and `Ideal.map_map`. The original source and hypotheses are retained.

## Second reading by D3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof import and proof body differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The only `sorryAx` reported for the theorem comes from the still-open imported dependency `lem-weil-pbc-adic-completion-mod-ideal`; the delivered file itself contains no `sorry`, axiom, unsafe, opaque, extern, or implemented_by. Verdict: pass.
3. Checked the proof route and edge cases. The coordinate identities, evaluation kernel theorem, and finite quotient transport prove exactly the original statement with all hypotheses retained; no new statement or split-off node was added. Verdict: pass.
4. Checked pruning and imports. `Mathlib.RingTheory.AdicCompletion.Completeness` is proof-only and required; the two public imports remain statement/definition imports. The former module-completion dependency is absent from the proof and from the node proof_deps. Verdict: pass.
5. Checked DAG agreement and unit route. The node proof and proof_deps match the declarations used in the Lean proof, and the unit's realized route is unchanged. Verdict: pass.

Changed after second reading: no proof or statement changes were needed; this section records the review.
