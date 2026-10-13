## What changed

Proved `Ideal.inf_ofList_le_mul_of_regular_quotient` in
`Sheaf.RingTheory.RegularQuotientIdealIntersectionAux` from Mathlib's
`RingTheory.Sequence.map_first_exact_on_four_term_right_exact_of_isSMulRegular_last`.
Applied it to the exact sequence `0 → I → R → R/I → 0`; the induced injection
`I/(gs)I → R/(gs)` gives the required inclusion. The existing signature, visibility,
imports and docstring are unchanged. Updated the node's proof, proof dependencies
and proof origin to this shorter route.

## Proved and sorry left

Closed the sole hole: `Ideal.inf_ofList_le_mul_of_regular_quotient`
(node `aux-regular-quotient-ideal-intersection-inclusion`).
No holes added; no `sorry` remains in the delivered module.
The proof uses weak regularity only, so in particular handles the empty list;
then both sides are the zero ideal. The zero quotient has no regular sequence
under the stated hypothesis, and requires no additional case assumption.
Local compilation is clean.

## No longer needed

The proof does not need the three planned dependencies:

- `def-weil-pbc-koszul-complex`, module `Sheaf.Paper.KoszulComplex`;
- `def-weil-pbc-koszul-regular-sequence`, module `Sheaf.RingTheory.KoszulRegularSequence`;
- `lem-weil-pbc-regular-sequence-koszul-regular`, module
  `Sheaf.RingTheory.RegularSequenceKoszulRegular`.

These nodes are removed from this node's `proof_deps`. They were not imported in
the original module, so no import line was removed. The only existing import,
`Mathlib.RingTheory.Regular.RegularSequence`, is needed for both the statement and proof.
This auxiliary node realizes no unit statement or step of `sk-thm-p1`; that unit's
route is unchanged. These dependencies may still be needed by other nodes.

## Where the brief, the DAG or earlier work was wrong

The Koszul chase is unnecessary for the regular-sequence hypothesis of this
statement: Mathlib already proves the exactness-preservation result needed here.
The original theorem docstring describes the valid planned Koszul argument;
the delivered proof instead follows the updated node's exact-sequence argument.
The referenced local Stacks source file is not present on this machine; the
completed proof and its mathematical ingredients are fully available in Mathlib.

## Second reading by S2

1. Compared the sole delivered module against the repository with `diff -u`.
   Only the existing theorem's proof body changes; its signature, visibility,
   docstring, module header and public import are byte for byte unchanged.
   No definitions or other modules are delivered. Verdict: pass.
2. Independently compiled the module and its scratch axiom probe through
   `lcompile.py`, both cleanly. `#print axioms
   Ideal.inf_ofList_le_mul_of_regular_quotient` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Scanned delivered Lean for forbidden
   declarations and `sorry`; none occur. Read the quotient exactness argument:
   the zero source forces the kernel class to vanish, and the final submodule
   membership is precisely membership in the product ideal. Verdict: pass.
3. No statements are split off and no new declarations or nodes are added.
   Checked the original statement's edge cases: the empty list generates the
   zero ideal, `I = 0` gives the zero inclusion, and `I = R` cannot satisfy
   regularity on the zero quotient. For a singleton, injectivity modulo `I`
   forces its coefficient into `I`, agreeing with the general argument.
   Verdict: pass.
4. Read Mathlib's exactness-preservation lemma and searched with different
   wording using Lean Finder, Loogle and `rg` on Mathlib and both project
   roots. No shorter independent intersection result was found; the equality
   theorem in `RegularQuotientIdealIntersection` already depends on this
   auxiliary, so it cannot replace the proof. The only import is needed by
   the statement, hence correctly public. All three former `proof_deps`
   appear under `No longer needed`; no source imports are removed and no
   module is claimed globally unreachable. Inspected `sk-thm-p1.json`:
   this auxiliary realizes no unit statement or step, and the unit's route
   stays intact. Verdict: pass.
5. Compared the node JSON with the repository: only `proof`, `proof_deps`
   and `proof_origin` change. The two proof steps describe the actual Lean
   argument, their empty `uses` union equals `proof_deps`, and their cited
   Mathlib origin is correct. The statement and Lean record are unchanged.
   There are no new nodes to audit. Verdict: pass.

Second reading changed only this report, adding the independent checks above;
the Lean proof and node required no repair. One hole closed, zero holes added.
