## What changed

Proved AlgebraicGeometry.Scheme.singletonTensor_normalization_evaluation with the same
public signature, visibility, docstring and import. The additive evaluation map is the
singleton product projection followed by AddEquiv.ulift.toAddMonoidHom; its pure-tensor
formula is exactly the normalization hypothesis.

Repaired return A (reviewer X-7a434, head 7a434abbc): removed the two pre-declaration
local instance attributes. Witness reuse now occurs only inside the proof, after an
explicit product-witness transport. The transport constructs a kernel-checked Eq.mp
term using congrArg and Subsingleton.elim; it does not alter any environment attribute
or theorem signature. The two proof-local class lets then avoid the expensive
comparison through tensor-pullback section types. The declaration-scoped option only
suppresses the auxiliary-name linter; it does not alter elaboration or exported instances.

Validation: lcompile.py compiled the repaired module in 27.4 seconds and its unchanged
direct importer Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeKernel in
8.7 seconds, without warnings or errors, in scratchpad/interface-check. The importer
used the repaired module's freshly compiled artifacts. The public signature and
docstring match the repository byte for byte; every Lean line is at most 100 characters.

Change record: coord/changes/singletonTensorNormalizationEvaluationLocalWitnesses.md.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.singletonTensor_normalization_evaluation
(node new-etale-singleton-tensor-normalization-evaluation).
No sorry remains in the item; zero holes or modules were added. This is a proof,
not a decomposition. No postponed theorem is used to supply the argument.

## No longer needed

None. The original public import supplies definitions appearing in the statement.
The node's singleton projection/evaluation route and its normalization dependency remain.

## Where the brief, the DAG or earlier work was wrong

The returned registrations were placed before the theorem. Despite being local,
they changed the product witnesses in its elaborated public type, causing the direct
importer EtaleAffineSingletonTensorDegreeKernel to exceed the 60-second limit.
The previous report's claim that this was purely local elaboration was therefore wrong.
The repair keeps the standard witnesses in the public signature and transports them
only in the proof. No direct-importer adaptation is required or delivered.

The earlier second reading describes the returned version and has been removed so that
the next independent reader can assess the repair. The mathematical route and DAG
statement remain correct. The construction covers n = 0, empty schemes and zero modules.

## Second reading by Q4

1. PASS: compared the delivered module with the repository by diff and compared the
   theorem signature byte for byte. The signature, visibility, docstring and sole
   public import are unchanged. No definitions, environment instance attributes or
   other modules are delivered. The declaration-scoped auxiliary-name linter option
   has no effect on the exported mathematical interface.
2. PASS: independently compiled the repaired module and a scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.singletonTensor_normalization_evaluation`.
   The only axioms are propext, Classical.choice and Quot.sound. There are no sorrys,
   forbidden declarations or hollow definitions. Read the metaprogram: it constructs
   an equality transport using Subsingleton.elim, congrArg and Eq.mp, then leaves a
   genuine proof goal; it does not disable kernel checking. Both witnesses reused by
   the proof are proofs of propositions, not arbitrary data from existence axioms.
   Recompiled the exact delivered source and the byte-identical repository direct
   importer in the isolated interface-check overlay: 6.4 and 7.0 seconds respectively,
   without warnings or errors.
3. PASS: no new declarations, split-off statements or holes. The additive map is the
   categorical product projection composed with AddEquiv.ulift.toAddMonoidHom, and
   hf supplies its required equation. This works at n = 0 and for empty schemes and
   zero modules; no nonzero, affine or bijective hypothesis is introduced.
4. PASS: read the normalization module and searched the local library for evaluation
   and additive projection routes. The proof already uses the direct Mathlib
   composition rather than a geometric comparison theorem or tensor induction.
   The sole public import supplies definitions used in the signature and is needed.
   The old proof_deps contains only the normalization node, which remains used;
   No longer needed is complete. Read dag/units/sk-prop-h2.json: its Kummer route and
   realized fields are unchanged, and this local evaluation bypasses no unit step.
5. PASS: read the item node and its normalization dependency. The existing proof,
   proof_deps and proof_origin describe precisely projection, ULift.down and the
   normalization equation. The proof-local witness transport is an elementary
   equality transport and requires no new mathematical dependency or node edit.

Changes by the second reader: added this independent review and fresh verification
results to report.md. No Lean, node or change-record repair was needed.
