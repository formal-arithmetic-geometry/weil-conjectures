## What changed

The signature and visibility of
`AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_residue_quotient_surjective`
are unchanged. Its proof now chooses finite generators of the maximal ideal, proves completion
flatness and quotient-map bijectivity using Mathlib, obtains affine-chart module gluing data,
and applies the new proved theorem `FormalGlueing.h0_prime_span_eq_top`.

The pushout comparison is made C-linear. Its range contains every compatible prime coordinate:
`pushout.inl (k h)` is the witness, by `pushout.inl_desc`. The span theorem and the C-linear
prime equivalence imply surjectivity of the completed comparison. Composing with
`Ideal.Quotient.mk_surjective` proves the original residue-quotient conclusion.

Added proof-only imports of `Sheaf.RingTheory.FormalGlueingH0PrimeSpan`,
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionFormalGlueingData`, and Mathlib's
`AdicCompletion.AsTensorProduct` (its Noetherian completion flatness instance).
All three delivered modules compile through lcompile.py without warnings.

The general span theorem is proved from the existing formal-gluing equivalence. The proof
constructs unit tensor tuples in H0 of canonical data, proves that a gluing morphism preserves
compatible tuples, and uses tensor induction and the prime component of an isomorphism.
No new algebraic assumption is left as sorry.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_residue_quotient_surjective`
(node `lem-sbc-completed-matching-ring-map-residue-quotient-surjective`). No sorry remains in
the item's module.

Also proved the new theorem `FormalGlueing.h0_prime_span_eq_top`
(node `lem-sbc-formal-glueing-h0-prime-span`); its private transport, canonical-tuple, and
morphism-compatibility helpers are all proved.

Added exactly one hole, as the whole proof of the public theorem
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_formalGlueingData_matching_projection`
(node `lem-sbc-punctured-completion-formal-glueing-data`). It constructs finite affine-chart
module data and a map from compatible families into the explicit section-ring pullback,
preserving the prime coordinate. It asserts no span or surjectivity property and does not
mention completedRingMap, its pushout, or its residue quotient. Its complete proof in words
is in the module and node. It accepts the supplied generators and needs no Noetherian
hypothesis; flatness and quotient bijectivity are proved separately in the main module.

This is a decomposition: one existing hole closed and one strictly intermediate geometric
hole added, net zero direct holes. The already-stated formal-gluing equivalence remains an
upstream dependency; its holes have not been copied into this delivery.

## No longer needed

Removed the explicit proof import `Mathlib.RingTheory.Ideal.Quotient.Operations`: its quotient
API is available from the statement imports of FormalGlueingH0PrimeSpan. This is a redundant
import removal, not pruning of that Mathlib module from the transitive closure.

No mathematical node or module is pruned. The old direct dependency on
`prop-weil-pbc-formal-glueing-equivalence` is now recorded transitively through
`lem-sbc-formal-glueing-h0-prime-span`, whose proof uses that equivalence. The existing
completed-ring-map and matching-section definitions remain necessary. The unit route stays
unchanged; the unit's realized statement and step lists are empty for this auxiliary node.

## Where the brief, the DAG or earlier work was wrong

The old single step says to reduce the canonical H0 comparison modulo the maximal ideal,
but the recorded theorem `FormalGlueing.exists_canonical_equivalence` supplies an equivalence
of module gluing categories, not a scheme-to-module chart construction or a statement about
the concrete section-ring pullback. Those are separate arguments. The delivery proves the
algebraic comparison consequence and exposes the missing geometric bridge.

Mathlib's completion flatness and residue-field-map bijectivity close the completion-property
steps; no new completion theorem is needed. The residue-field map is transported across
`AdicCompletion.maximalIdeal_eq_map` using a dependent quotient-map argument.

Sources read: Stacks [0BLH](https://stacks.math.columbia.edu/tag/0BLH), first two proof paragraphs,
and [05ER](https://stacks.math.columbia.edu/tag/05ER), canonical comparison Psi and its final
cokernel observation; [05EM](https://stacks.math.columbia.edu/tag/05EM) explains the canonical H0
identification. Local Mathlib and the existing FormalGlueing modules were read for signatures.
LeanSearch returned HTTP 500 (recorded unavailable); LeanFinder gave completion and gluing
results with different statements; Loogle found generic span lemmas; Mathlib grep found no
formal-module-gluing bridge. Local rg found no exact existing prime-span or chart-data theorem.
All remote queries are recorded in searches.jsonl.

The blueprint ancestor script reports None for the item's recently-created ancestry. The
new nodes therefore retain the explicit ancestor of the existing completed-ring-map node,
`sbc-thm-spreading-finite-etale-galois`, and its recorded route, extended by this item's chain.
No existing blueprint fields were changed.

Edge cases: the general span proof works for t = 0, zero generators, and zero modules, since
its tuple equations and tensor induction impose no nonemptiness condition. For the geometric
bridge, f generating the maximal ideal guarantees the correct cover even for t = 0; then U
is empty, the chart equations are vacuous and the matching pullback retains the completed
coordinate. Finite schemes with zero section rings use the same affine and sheaf arguments.

## New nodes

`lem-sbc-formal-glueing-h0-prime-span` is in
`lean/Sheaf/RingTheory/FormalGlueingH0PrimeSpan.lean`. It states that completed coordinates of
H0 families span the prime module under the usual flatness and quotient hypotheses. Its proof
from the existing 05ER equivalence is complete. This is a module theorem, independent of
schemes, ring pushouts, and residue quotients.

`lem-sbc-punctured-completion-formal-glueing-data` is in
`lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedCompletionFormalGlueingData.lean`. Its sole
remaining hole is the chart construction and compatible-family map, sourced from 0BLH's
construction and 05EL's H0 equations. It is strictly the geometric part of the argument.

Both new nodes are under dag/nodes/sec-smooth-base-change, with the item's chapter and unit,
actual search records and self-contained statements. The item's node copy records the Lean
proof route and the two new dependencies. No change record is needed: no existing signature,
visibility, definition, public import, instance or file-level option was changed, and there
are no forced adaptations.

## Second reading by G4

1. **Statements and interfaces.** Compared the delivered completed comparison module with the repository version byte for byte in the theorem signature; it is unchanged. The two added theorem signatures match their DAG node statements and introduce no altered existing declarations. Verdict: pass.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py --all`. The completed comparison and H0 span theorem have no `sorry`; the geometric bridge has exactly the named `exists_formalGlueingData_matching_projection` sorry recorded in its node and report. No forbidden declaration forms occur. Verdict: pass, with the documented split hole.

3. **New statements.** Checked the H0 span statement on empty generator families, zero modules, and the tensor induction edge cases; its hypotheses and conclusion are exactly those used by the comparison proof. The geometric bridge asserts only existence of chart data, a linear equivalence, and the projection equation, and makes no hidden surjectivity claim. Verdict: true and strictly intermediate as stated.

4. **Pruning and imports.** The proof uses the formal-gluing equivalence, the chart-data bridge, completion flatness/residue bijectivity, and the pushout comparison. The removed quotient-operations import is redundant; all remaining imports are used by declarations or proofs. The unit route and existing definitions remain in place. Verdict: pass.

5. **DAG agreement and sources.** The item node proof steps, `proof_deps`, and `proof_origin` follow the Lean proof. Both added nodes contain their statements, source locations, proof steps, searches, and Lean records; the split theorem's docstring gives the complete construction argument. Verdict: pass.

Changed during second reading: added this review section only; no Lean signatures or proofs were altered.
