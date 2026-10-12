## What changed

Replaced the proposed two-hole decomposition with a proof of
`AlgebraicGeometry.proper_existence_maximal_failure` from existing library declarations.
The target signature and all existing public imports are byte-for-byte unchanged. Added
three proof-only imports: `NoetherianQuasicoherentSubmodules`,
`FormalCompletionFullyFaithfulProper`, and `GrothendieckExistenceProjective` under
`Sheaf.AlgebraicGeometry`. The latter handles only the empty-scheme case.

The proof first identifies the quotient-kernel completion ideal with the ideal used by
proper full faithfulness. It takes a maximal element of the set of kernels of failing
closed immersions using the existing ACC theorem. An empty chosen subscheme contradicts
projective existence, since its unique map into dimension-zero projective space is a
closed immersion. A nonzero ideal quotient has a strictly larger kernel: equality would
make its inclusion an isomorphism and force its ideal to be zero. Maximality then gives
completion equivalence on every such quotient. Updated the existing node's proof,
proof_deps, and proof_origin to this actual route.

Removed both proposed new modules and nodes before delivery. No new statement, definition,
change record, or forced adaptation is delivered.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.proper_existence_maximal_failure`
(node `lem-weil-pbc-proper-existence-maximal-failure`). There are no direct sorries left
in the delivered module and no holes added elsewhere. The proposed holes
`AlgebraicGeometry.proper_existence_maximal_failure_core` and
`AlgebraicGeometry.proper_existence_maximal_failure_quotients` are removed, not counted
as closures of baseline holes.

This is a proof from existing stated dependencies. Its axiom audit is
`[propext, sorryAx, Classical.choice, Quot.sound]`: existing ACC, proper full faithfulness,
and projective existence dependencies remain open. Thus it is not an axiom-complete proof
of the target. The delivery adds no new split statement; it closes one direct hole.
Closure-wide progress is determined by the maintainer's pinned sorry ledger, not by this
module-local count.

## No longer needed

Removed the proposed proof-only imports of
`Sheaf.AlgebraicGeometry.GrothendieckExistenceMaximalFailureCore` and
`Sheaf.AlgebraicGeometry.GrothendieckExistenceMaximalFailureQuotients`, and omitted their
uncommitted modules and nodes. No import present in the repository version was removed.

Every unused old proof_deps entry is removed from this item's proof plan:

- `lem-weil-pbc-closed-immersion-coherent-equivalence`
  (`Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`): the proof considers
  failing closed immersions directly, avoiding supported-module transport.
- `lem-weil-pbc-closed-immersion-factor-ideal-inclusion`: no factorization lift is needed;
  the canonical quotient immersion already supplies the map.
- `lem-weil-pbc-module-pullback-ideal-quotient`
  (`Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`): the ideal comap composition
  formula suffices, without any module pullback/quotient comparison.

These are dependencies pruned from this proof, not a claim that their modules leave the
whole targets' import closure. No global module pruning is asserted.

## Where the brief, the DAG or earlier work was wrong

The proposed core supplied only a failing subscheme, with no maximality invariant. The
quotient helper then claimed success on all nonzero quotients from failure alone.
STATEMENT-DISPUTED: its proof used maximality absent from its hypotheses. Keeping those
two holes would conceal the central maximality argument rather than prove it.

Both proposed node statements were non-self-contained labels, their proof steps merely
said the proofs were postponed, their lean.statement fields were not Lean signatures,
and their copied review records did not certify the new statements. The target node's
proof_deps had not been updated to describe the proposed proof. Removed this proposal
instead of delivering these faults.

The original existing plan was usable: its ACC declaration includes precisely the
maximal-ideal clause needed. The empty case can use the already stated projective theorem,
with an actual closed immersion and the actual structural map; it needs no new hole.

## Second reading by C3

1. Compared the delivered module against the repository with `diff -u` and checked the
   complete declaration signature as a string: it is byte-for-byte identical. Only the
   proof, its proof explanation, and three plain imports changed. No existing definition,
   signature, visibility, public import, or target statement changed. No relevant open
   change record was found. Verdict: pass.
2. Compiled the original proposal and found overlong-line warnings in both new modules.
   After repair, compiled the final module cleanly with `lcompile.py`. A scratch copy with
   `#print axioms AlgebraicGeometry.proper_existence_maximal_failure` compiled and showed
   only the three permitted axioms and sorryAx from existing open dependencies. Scanned
   the delivered source: no sorry, axiom, unsafe, opaque, implemented_by, extern, hollow
   definition, or arbitrary witness used to define data. The selected formal objects and
   closed immersion are existential witnesses used solely in a theorem proof. Verdict:
   pass, conditional on the existing open dependencies as explicitly reported above.
3. Read both proposed split statements and rejected the missing-maximality quotient
   claim; removed both. Searched the library with different terms and used msearch
   leansearch, leanfinder, and grep: LeanSearch was unavailable; the other searches found
   no direct formal-completion failure reduction. Read the existing ACC, proper full
   faithfulness, and projective existence statements and used them instead. There is no
   new split statement to review. Edge cases: the identity immersion makes the failing
   set nonempty; an empty chosen scheme is ruled out by the projective theorem; K = 0 is
   excluded exactly where strictness needs it; K = top is allowed and its empty quotient
   is included; zero rings and I = 0 or top are not excluded by any new hypothesis.
   Every Noetherian witness on a quotient is accepted by proof irrelevance. Verdict: pass.
4. Read Stacks Tag 088C, first two proof paragraphs, and the unit sk-thm-p1 realized
   statement/steps. The route still chooses a maximal failing ideal and reduces to its
   closed subscheme. Indexing failures by closed-immersion kernels makes the quotient
   argument direct; equal kernels imply the needed isomorphism by Mathlib. The empty
   case specializes existing projective existence, not general proper existence. No
   realized unit node is bypassed; all three proof imports are actually used and plain.
   The original public imports support the unchanged signature. All three unused old
   proof_deps are listed above. Verdict: pass.
5. Compared the final node with its repository version: only proof, proof_deps, and
   proof_origin differ. Its proof_deps are the union of the uses in its new proof steps
   and match the Lean: Noetherianity, ACC, proper full faithfulness, projective existence,
   proper composition, closed-immersion composition, canonical ideal quotients, and
   equal-kernel isomorphisms. There are no new nodes or change records. Verdict: pass.

Second reading changed the proposed proof into a real ACC/maximal-kernel reduction,
removed both split modules and nodes, supplied the empty-case argument via projective
existence, repaired the target node's route, and corrected the progress report. The
unchanged theorem now has a complete local proof from existing library statements.
