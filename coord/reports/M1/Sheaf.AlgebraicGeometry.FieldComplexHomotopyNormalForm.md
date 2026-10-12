## What changed

Marked `AlgebraicGeometry.Scheme.Modules.homotopyEquiv_of_single_field_homology`
STATEMENT-DISPUTED: the vanishing hypothesis ranges over natural numbers even though
P is indexed by integers. The theorem signature and its existing sorry are unchanged.
Added three fully proved private lemmas in the item's module to certify a counterexample,
with proof-only imports of `Mathlib.Algebra.Homology.SingleHomology` and
`WeilConjectures.AlgebraicGeometry.Modules.FreeComplex`.

For every field R, let A be the rank-one free sheaf on Spec R and let P be A placed in
degree -1. Take i = r = 0. Every nonnegative homology sheaf of P is zero, so the hzero
hypothesis holds; its degree-zero homology is finite locally free of rank zero, so hrank
also holds. The purported homotopy equivalence would induce an isomorphism in degree -1
between A and zero, contradicting A's rank one.

The private lemma `counterexample_to_single_field_homology` proves this entire
existential counterexample in Lean, not just a necessary condition. It uses
`negative_single_nonnegative_homology_zero` and `no_equiv_negative_single`.
The scratch check at `scratchpad/Obstruction.lean` prints axioms for all three:
only propext, Classical.choice and Quot.sound. The delivery tool also probes them.

## Proved and sorry left

Holes closed: 0. Holes added: 0. Split off: 0.

The existing sorry remains in
`AlgebraicGeometry.Scheme.Modules.homotopyEquiv_of_single_field_homology`
(node `new-field-complex-homotopy-normal-form`). This statement is false as written.
The three private counterexample lemmas named above are fully proved without sorry.
No false lower statement was introduced to disguise a proof of the disputed theorem.

## No longer needed

None. No existing import, node or module is pruned. The two added imports are needed
by the certified counterexample: single-complex homology identifies H^-1 with A;
the free-complex rank lemmas show A is nonzero and H^0 has rank zero.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `new-field-complex-homotopy-normal-form` calls P a bounded complex
with sole cohomology, but its Lean signature imposes neither a negative-degree
vanishing hypothesis nor a lower support bound. Boundedness alone does not fix this:
the counterexample is already a bounded single complex of finite free sheaves.
No true splitting lemma can imply the current conclusion from the current hypotheses.

The parent `nonempty_homotopyEquiv_single_field_fibre` in
`Sheaf.AlgebraicGeometry.FiniteFreeSingleFieldFibre` does have hge : P.IsStrictlyGE 0,
which was lost at this split. A correction could add the corresponding lower support
bound to this helper, deriving it for the termwise pullback at the parent's call, or
require vanishing in every integer degree other than i. Such an interface repair
requires the forced adaptation and change-record process, and is not attempted in
this delivery. No target or intermediate signature was changed.

The node has no proof dependencies to import: its single step says to split into
contractible boundary summands and the sole cohomology summand. Applied to the
counterexample, that argument preserves the degree -1 cohomology summand and cannot
produce the proposed degree-zero single complex. The unit route is unchanged.

## Second reading by M1

1. Compared the sole delivered module with the repository using `diff -u`.
   The existing theorem signature, docstring, visibility and sorry body are byte
   for byte unchanged. There are no definitions or change records. Only two
   proof-only imports, three private proved counterexample lemmas and the
   STATEMENT-DISPUTED comment were added. Verdict: no accidental interface change.
2. Compiled the delivered module and the independent scratch axiom check with
   lcompile.py. The only remaining sorry is the original disputed theorem.
   The counterexample lemmas use only propext, Classical.choice and Quot.sound;
   no forbidden declaration or hollow definition occurs. Verdict: the
   counterexample is certified, while the original theorem remains unproved
   and false; this delivery is a dispute, not proof progress.
3. No statements were split off and no holes were added. Checked the private
   helpers from the explicit single complex in degree -1: all natural-degree
   homology vanishes; its zero degree has rank zero; its negative homology has
   rank one. In particular the rank-zero edge case already refutes the item.
   Searched Lean sources for related normal forms and rank lemmas, and used
   msearch loogle with HomotopyEquiv.toHomologyIso: the existing Mathlib result
   is used directly. Verdict: no replacement restatement or false lower lemma.
4. Read the parent FiniteFreeSingleFieldFibre, the imported rank lemmas and the
   unit sk-thm-picard-perfect, including its realized field (currently empty).
   The parent's lower support bound was lost in this helper. No shorter proof
   can establish a refuted statement. The new imports are proof-only and used;
   all existing imports serve the public signature. No old proof dependency
   is removed (the node's proof_deps is empty), and no unit route is bypassed.
   Verdict: no pruning or route change; the upstream interface needs repair.
5. Read new-field-complex-homotopy-normal-form.json. Its statement and Lean
   record match the unchanged theorem; proof_deps remains empty. Its proof
   remains an unimplemented splitting plan and cannot prove this signature,
   since it incorrectly assumes sole cohomology. The report identifies that
   error explicitly. No node is newly introduced or silently claimed proved.
   Verdict: existing node metadata remains unchanged; the plan is disputed.

Changes by this second reader: appended this review and independently compiled
an axiom-printing scratch copy of the actual delivered declarations. No Lean
proof or public interface needed alteration. Holes closed: 0 of 1; holes added:
0; split off: 0; pruned: none.
