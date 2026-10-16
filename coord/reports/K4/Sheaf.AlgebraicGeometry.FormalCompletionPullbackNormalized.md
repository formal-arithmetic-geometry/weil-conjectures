## What changed

Proved `AlgebraicGeometry.exists_formalCompletionPullback_normalized` in
`lean/Sheaf/AlgebraicGeometry/FormalCompletionPullbackNormalized.lean`.
After eliminating the ideal and module equalities, the proof takes the inverse of
`completionPullbackIso` at the supplied coherent module. Its component at each level
is the inverse of `powerQuotientIso`; the existing `powerQuotientIso_π` equation and
isomorphism cancellation prove the required normalization. The statement, imports,
and definitions are unchanged. This implements the existing node's proof route.

Validation: the module compiled cleanly through `lcompile.py` in 2.0 seconds.
An independent `#print axioms` compile reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. The source proof of Stacks 0887 and the completion identity used in 088B were read
in `literature/stacks-project/coherent.tex`. Searches through LeanFinder, Loogle,
and Mathlib grep, together with local searches of both library roots, found the
existing project comparison as the shortest route. Loogle confirmed the standard isomorphism cancellation API; the proof uses
`Iso.hom_inv_id` together with associativity and the identity law. No extra hypotheses on X are used.
The proof also applies to empty schemes, zero modules, and zero or unit ideals,
because it uses the general quotient-comparison identity without case exclusions.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_formalCompletionPullback_normalized`
(node `lem-weil-pbc-formal-completion-pullback-normalized`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0.
No statements were split off and no new theorem with `sorry` was introduced.

## No longer needed

None. Every existing import remains needed by the statement or by the
`completionPullbackIso` and `powerQuotientIso_π` proof. The node retains its existing
proof dependencies, and no node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or proof-route correction was needed: the node's planned inverse
comparison and projection cancellation suffice. The source checkout has retired
`Sheaf.AlgebraicGeometry.FormalSystemsPullback` to an upstream re-export, whereas
the published compiled baseline still contains the original Sheaf implementation.
The proof uses the existing `import all` and compiles against that published baseline.
A separate three-module import experiment confirmed that `import all` of a wrapper
will not expose private declarations from its upstream public import. Once the
upstream sync is published, this proof's import must point directly to
`WeilConjectures.AlgebraicGeometry.FormalSystemsPullback` with `import all`.
That direct import currently fails because its compiled object does not exist;
no library file was copied or changed to work around the build lag. The delivery
retains the original import, as the project's published-baseline rule requires.

## Second reading by K4

1. **Statements and signatures.** Compared the delivered module with the repository version and
   the node's `lean.statement`; the theorem signature is byte-for-byte unchanged. Verdict: pass.
2. **Proof validity.** Compiled the module with `lcompile.py`; it has no errors, warnings,
   `sorry`, forbidden declarations, or hollow definitions. The proof uses only the existing
   `completionPullbackIso` and `powerQuotientIso_π` declarations. Verdict: pass.
3. **Split statements.** No statements were split off and no new nodes were added; therefore
   there are no new truth or strength issues to check. Verdict: pass.
4. **Pruning and imports.** Checked the public imports against the theorem signature and the
   private proof dependencies. All imports are used, and the proof follows the unit route through
   the existing formal-systems pullback comparison. Verdict: pass.
5. **DAG agreement.** The node's declaration, proof route, proof dependencies, and proof origin
   agree with the Lean proof; the unit `sk-thm-p1` route remains represented by the existing
   formal-systems pullback node. Verdict: pass.

No code, statement, import, or DAG change was needed during second reading; only this review
section was added to the report.
