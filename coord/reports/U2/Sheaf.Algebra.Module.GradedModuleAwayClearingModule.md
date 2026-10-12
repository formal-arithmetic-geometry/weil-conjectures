## What changed

Proved `LocalizedModule.gradedModuleAwayClearingModule` in
`Sheaf.Algebra.Module.GradedModuleAwayClearingModule` without changing its signature
or public imports. Represent the given fraction, handle a zero denominator by
subsingleton localization, and construct the equal-degree preimage
`g^(n*(deg(f)-1)) • v / f^(n*deg(g))`. The final equality follows by multiplying
by the unit `f^(n*deg(g))`, computing both sides as `V/1`, and cancelling.
The node's proof and proof_origin now describe this actual argument.

The final file compiles without warnings through lcompile.py. A separate scratch
copy with `#print axioms LocalizedModule.gradedModuleAwayClearingModule` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed: `LocalizedModule.gradedModuleAwayClearingModule`
(node `lem-weil-pbc-graded-module-away-clearing-module`), the module's only hole.
Holes added: none. Sorries left in the delivery: none. This is a full proof,
not a decomposition, and does not depend on a theorem with `sorry`.

## No longer needed

No imports, existing nodes, or existing modules are pruned. Both original public
imports are required by the unchanged statement. The rejected earlier
`gradedModuleAwayClearingModule_ambient` restatement and its proposed node are
absent; no replacement intermediate statement is introduced. The proof does not
use module semilinearity or an explicit inverse formula, but those hypotheses
remain in the original signature.

## Where the brief, the DAG or earlier work was wrong

The previous attempt renamed the entire target into an unproved intermediate
statement. This delivery replaces that with the complete fraction calculation.
The existing plan's semilinearity computation is unnecessary: S-linearity,
preservation of denominator-one fractions, and unit cancellation suffice.
There is no statement or definition correction and no forced adaptation.

The local literature source file is absent on this machine; the source was read
at https://stacks.math.columbia.edu/tag/01M4, proof of (1)(h). The construction
follows that fraction calculation and keeps the unit's route. The case split
handles zero denominators even in rings with zero divisors; the same arithmetic
also covers zero numerators, n=0, and deg(f)=1.


## Second reading by U2

1. **Unchanged interface: pass.** Compared the sole delivered Lean module with
   the repository using diff and a byte comparison of the complete theorem
   signature. Every binder, let-bound family, hypothesis, conclusion, universe,
   visibility, and both public imports is unchanged. There are no definitions,
   adaptations, new declarations, or change records. Restored the repository's
   existing docstring, which the first worker had unnecessarily rewritten.
2. **Proof and axioms: pass.** Independently compiled the delivered file with
   lcompile.py, with no errors or warnings. Regenerated a scratch copy from the
   actual delivered source and printed the theorem's axioms: only propext,
   Classical.choice, and Quot.sound. Scanned the delivered source: no sorry,
   axiom, unsafe, opaque, implemented_by, or extern. In the nonzero denominator
   branch, degree uniqueness is applied to the denominator, never to a possibly
   zero numerator. The final cancellation uses hfunit in S_g, not cancellation
   in S or M.
3. **Split statements: pass, none.** No new theorem or node and no added hole.
   Checked the construction for n=0 (V=v and denominator 1), deg(f)=1 (V=v),
   v=0, the zero ring, and g^n=0. The last two are handled by subsingleton
   localization; no domain or nonzero numerator assumption is introduced.
4. **Shortest route and pruning: pass.** Read Stacks tag 01M4, proof of (1)(h),
   and the local degreeZeroFractions definition. Rechecked Mathlib's localized
   module cancellation API through Loogle (LocalizedModule.mk_cancel), and
   searched local Lean for degree-zero lifting, clearing, and localization
   surjectivity. AwayDegreeZeroLift concerns a polynomial ring and one fixed
   denominator, so cannot replace this argument for arbitrary S and f,g.
   The proof already uses Mathlib's fraction equality, graded powers, and unit
   cancellation directly. Both imports occur in the signature and remain
   public. The four old proof_deps are all retained and used; the no-longer-needed
   list is complete (none). Read sk-thm-reduction.json, including realized:
   this algebraic helper lies below its symmetric-product finite step, and
   proving it changes none of the unit's realizations or routes.
5. **DAG agreement: pass.** The node's recorded Lean statement is byte-identical
   to the delivered signature. Only proof and proof_origin differ from the
   repository node; proof_deps equals the union of the three steps' uses.
   Checked each step against the code: representation/subsingleton and degree
   uniqueness; construction of V/f^(n*deg(g)); then the scalar identity,
   S-linearity, mk_cancel, and unit cancellation. The node accurately records
   that semilinearity and the explicit inverse formula are not needed.

Second reading changed only the existing docstring back to the repository text
and added this review. The Lean proof was read and retained unchanged. Closed
LocalizedModule.gradedModuleAwayClearingModule (1 hole); added 0 holes; split off
0 statements; pruned none. Source read: https://stacks.math.columbia.edu/tag/01M4.
