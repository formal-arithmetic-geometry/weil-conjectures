## What changed

Marked `proper_flat_boundedPresentation_model_baseChange` STATEMENT-DISPUTED.
Its existing signature and sorry are preserved. Added the proved private diagnostic
`single_negative_homology_obstruction`, using a proof-only import of
`Mathlib.Algebra.Homology.SingleHomology`. The diagnostic transports homology
through the pullback-identity natural isomorphism and the single-complex homology
isomorphism. It uses no project theorem with sorry.

## Proved and sorry left

Closed 0 of the item's 1 holes; added 0 holes; split off 0 statements.
Remaining: `AlgebraicGeometry.Scheme.Modules.proper_flat_boundedPresentation_model_baseChange`
(node `lem-pc-proper-flat-bounded-presentation-comparison-core`).
The private diagnostic is proved and compiles. This is a disputed-statement
report, not a proof or decomposition of the false statement.

## No longer needed

None. No imports, nodes or modules were pruned. The existing public imports
are required by the unchanged signature. The added proof-only Mathlib import
provides the single-complex homology computation used in the diagnostic.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the Lean statement quantifies over an arbitrary bounded
termwise flat quasi-coherent finitely presented complex C. There is no assumption
linking C to F or to the derived direct image. The node's informal statement
instead refers to a model *produced by the proper direct-image construction*.
These are different claims.

Concrete counterexample to the first conjunct: take X = T = Spec(k), for a field
k, f the identity, F the structure sheaf, U the whole affine scheme, and C the
single complex with the structure sheaf in degree -1. Take a = -1 and b = 0.
This complex is strictly bounded as requested; its terms are either zero or
rank-one finite free sheaves, hence flat, quasi-coherent and finitely presented.
The identity is proper, quasi-compact and locally of finite presentation, and
F is flat and finitely presented. Categories of sheaves of modules have injective
resolutions. Pull back along the identity and evaluate at i = -1. The homology
is the nonzero structure sheaf, contradicting IsZero. The private Lean diagnostic
checks precisely the identity-pullback and single-complex homology calculation
for any nonzero scheme module; the concrete scheme and finiteness conditions
in this paragraph are a mathematical counterexample, not a formalized instance.

Independent counterexample to the second conjunct: use the same geometric data
and the zero complex C, with a = b = 0. In the identity cartesian square and q = 0,
the assertion identifies the zero object with the nonzero structure sheaf,
since zeroth higher direct image for the identity is the identity functor.
Thus adding a nonnegative lower bound would not repair the statement.

`exists_proper_flat_boundedPresentation_model_core` in
`Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModelCore` returns only
structural properties of C and also loses the relation to F. The only caller,
`exists_proper_flat_boundedPresentation_model` in
`Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel`, extracts those
properties and applies this theorem to the witness. Fixing just this theorem
by adding a derived-model hypothesis would leave that caller without a proof
of the hypothesis. The correction must retain the derived identification in
the structural construction and carry it into the comparison, or reorganize
that construction so that its existential witness includes the identification.
Neither a new universally quantified comparison lemma nor renaming the current
statement can fix this loss of information. No signature was changed and no
forced adaptation was made in this delivery.

The unit `sk-thm-picard-coherence` requires a model representing Rf_* F and
compatible with arbitrary base change; the diagnostic does not bypass its route.
The item's node currently has no proof dependencies, and its one proof step
("Apply derived base change ...") cannot establish the missing identification
from the existing hypotheses. Searches ran through msearch with LeanFinder,
Loogle and grep; they located Mathlib's single-complex homology isomorphism and
homology functor, which suffice for the diagnostic rather than the false claim.

## Second reading by A2

1. Compared the complete delivered module with the repository using `diff -u`.
   The existing theorem signature, visibility and sorry body are byte for byte
   unchanged. The only Lean additions are the private proved diagnostic, its
   proof-only import and the STATEMENT-DISPUTED comment. There are no definition
   changes, change records or adaptations.
2. Compiled the delivered file with lcompile.py: exit 0, no warnings. Compiled
   a scratch copy with explicit `#print axioms` for both declarations. The private
   diagnostic uses exactly propext, Classical.choice and Quot.sound. The original
   theorem additionally uses sorryAx, as reported. There is exactly one sorry,
   in that existing named theorem, and no forbidden declaration or hollow data.
   The diagnostic constructs only canonical isomorphisms and chooses no witness
   from an unproved existence theorem.
3. No statements were split off and no holes were added. Independently checked
   the counterexample: the single complex in degree -1 is bounded between -1
   and 0, with zero or rank-one free terms over Spec(k); its degree -1 homology
   after identity pullback is the nonzero structure sheaf. The supplied private
   proof checks the homology transport, rather than claiming to formalize all
   geometric hypotheses. Also checked the zero-complex counterexample to the
   second conjunct. Repeated a Loogle search for the single homology isomorphism
   and searched existing Sheaf modules for single-complex computations: the
   diagnostic uses the existing Mathlib result directly.
4. No proof of the unchanged false theorem can be obtained by a shorter route.
   Read the structural-core theorem and its sole comparison caller: neither
   supplies the missing identification of C with the derived direct image.
   All three public imports are needed for the existing signature, and the
   new private import supplies the diagnostic's homology isomorphism. No old
   proof dependencies exist, so the No longer needed section is complete.
   Read sk-thm-picard-coherence: it requires a representing complex; its route
   and realized fields are untouched (the existing realized lists are empty).
5. Read the item's node in full. Its lean.statement matches the unchanged
   signature; proof_deps is empty. Its informal statement and planned proof
   presuppose the missing derived-model identification. This is the recorded
   statement dispute, not a realized proof, so no proof/proof_deps/proof_origin
   changes are claimed or delivered. There are no new nodes to reconcile.

Second reading changed only this report, adding the independent review and
axiom evidence. The Lean diagnostic and dispute marker were correct as written.
Verdict: deliver as a disputed statement; proved 0 of 1, added 0 holes,
split off 0, pruned none. Repair requires preserving the derived identification
across the construction and comparison, not proving the current universal claim.
