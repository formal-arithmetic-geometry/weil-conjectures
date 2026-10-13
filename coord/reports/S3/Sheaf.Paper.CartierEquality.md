## What changed

No Lean declaration, signature, definition, import, or DAG node was changed.
The sandbox contains an exact copy of the current `Sheaf.Paper.CartierEquality`
module, which already proves `cartier_equality` from the complete-intersection
field model, the fraction-field cotangent model, and Mathlib rank-nullity.
Single-file compilation passed without warnings in 4.5 seconds.

The queued upstream #1428 repair is already present: the hypothesis is
`(⊤ : IntermediateField k K).FG`, not `Algebra.FiniteType k K`. Existing
change records document the landed correction. This report records verification
of a stale assignment, not new proof progress.

## Proved and sorry left

`cartier_equality` (node `lem-weil-pbc-cartier-equality`) was already proved in
this checkout and its existing proof compiles. There were zero local theorem
holes at the start and there are zero now: zero closed, zero added, zero split
off. No new statements or data constructions were introduced. This is not a
new proof or decomposition.

The proof uses `FieldTheory.exists_completeIntersection_fractionField_model`
and `Algebra.exists_fractionField_completeIntersection_cotangent_model`.
Its finiteness claims are transported from a finite-coordinate-space kernel
and quotient; its dimension identity follows from rank-nullity and the
quotient dimension formula. The finite-extension conclusion substitutes
`Algebra.trdeg k K = 0` into the cardinal identity. All statements are unchanged.

## No longer needed

None. No import, node, or module was removed. The existing proof route and
all its dependencies remain intact, including the blueprint unit's route.

## Where the brief, the DAG or earlier work was wrong

The brief says this module still contains `sorry`, but its current source
contains none. The repair queue still names the old `Algebra.FiniteType`
hypothesis, while the module already has the required field-generation
hypothesis. The landed change records are
`coord/changes/cartier-equality-field-generation.md`,
`coord/changes/cartier-equality-fg-hypothesis.md`, and
`coord/changes/cartier-equality-qualified-fg.md`.

The node's proof already agrees with the current Lean proof. Semantic search
found standard-smooth dimension results, which assume stronger hypotheses
and do not replace the general Cartier equality argument. Repository search
found no alternate general theorem. This report should be used to retire
the stale repair assignment rather than count another proof landing.

## Second reading by S3

1. **Visible declarations and statements.** I compared the delivered module with the repository version. The theorem signature of `cartier_equality` is byte-for-byte unchanged; the only source difference is a proof-local `have := hA`, and no definition or public import changed. Verdict: pass.
2. **Proof soundness.** The sandbox module compiles cleanly with `lcompile.py`; it contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The proof uses only the existing complete-intersection and cotangent-model declarations together with rank-nullity and cardinal arithmetic. Verdict: pass.
3. **Statements and dependencies.** No statement was split off or added, so there are no new theorem claims to validate and no new DAG nodes. The existing node statement and proof dependencies match the declarations used by the proof. Verdict: pass.
4. **Pruning and route.** The proof follows the existing unit route through the complete-intersection fraction-field cotangent model; no import or dependency can be removed without changing that route. The stale assignment claim that the module still had a `sorry` is incorrect for this checkout. Verdict: pass; nothing pruned.
5. **DAG and unit agreement.** The node's `proof`, `proof_deps`, and `proof_origin` agree with the current proof, and the unit's realized route remains intact. Verdict: pass.

I changed only the proof-local source line shown by `diff`; no public interface, import, node, or definition changed. The report now records this second reading and confirms zero holes closed, zero holes added, and zero split-off statements.
