## What changed

Completed `AlgebraicGeometry.ProEtale.integral_lfp_local_torsion_charts` in
`Sheaf.Paper.IntegralLfpLocalTorsionCharts`, with its statement unchanged.
Added proved private helpers for scalar-chart transport, cover refinement, binary
sums, cyclic pivots, and strong induction on the source rank of a finite matrix.
The induction splits a pivot cokernel and a smaller Schur-complement cokernel,
then combines their charts. The final proof transports the resulting charts to
the precise image and underlying-set inverse images in the original signature.

Added proof-only imports of `FiniteBiproductPivot` (including its private basis
split), `IntegralRegularCoefficientPullback`, `SheafPullbackForgetComparison`,
Mathlib's preservation-of-images API, and the ultrametric total-separation API.
Updated the existing node's proof, proof dependencies and proof-origin note to
match the compiled argument. All existing declarations and public imports retain
their signatures and visibility. No definition repair or consumer adaptation is
needed. Preflight flags the file-local scope and local-instance commands;
`coord/changes/integral-lfp-local-torsion-proof-environment.md` records their
exact old/new forms and the unaffected downstream consumers. The existing private `resolutionRationalLF`, used by
`IntegralLfpLocallyFreeResolution`, is retained unchanged.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.ProEtale.integral_lfp_local_torsion_charts`
(node `lem-weil-pbc-integral-lfp-local-torsion-charts`).

The item now contains zero `sorry`. Added zero holes and zero split-off modules.
Every new private helper has a complete Lean proof or construction. The zero-module
freeness argument is local rather than a duplicate named declaration.
The complete file compiles without warnings in about 36 seconds, and the
delivery axiom probe passes.

## No longer needed

Removed redundant direct proof-only imports of
`Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`,
`Sheaf.Paper.GeometricFieldProEtaleEvaluation`, and
`Sheaf.Paper.IntegralMatrixAnalyticCover`. Their declarations remain available
through the retained proof imports, so no module is pruned from the closure.
`FiniteBiproductPivot` is retained as `import all` to use its private basis split.

Removed the direct proof-dependency edge to
`lem-weil-pbc-geometric-field-proetale-evaluation`; it remains a transitive
mathematical dependency through the analytic-cover theorem. This is the only
removed edge in the old `proof_deps`. The proof does not need a new simultaneous
diagonalization theorem: it combines binary scalar charts directly while
inducting on source rank. Existing proved diagonalization helpers retain their
signatures. Two unused new transport helpers were removed before submission.
Finite-discrete quotient results and continuous coefficient realizations remain
used by the retained arithmetic helpers.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The returned delivery identified `chartFreeZero` as a duplicate
of the existing downstream `resolutionFreeZero`; because that downstream module imports this
module, the repair keeps the proof local and does not introduce a cyclic import. The previous
node described simultaneous diagonal form
and left its assembly and pullback transports open. A simpler assembly proves
local scalar charts directly, using the maximum of two bounds at each induction
step. The generic one-sided pivot interface does not retain both divisions, so
the proof uses its explicit finite-biproduct basis split with separately proved
column division. Forgetting abelian groups need not preserve arbitrary colimits;
the underlying-set pullback comparison is justified here by terminal objects in
the relevant Kan-extension indexing categories, rather than by that false general
preservation claim. The blueprint unit route is unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the whole delivered module with the read-only repository version.
   Every pre-existing private declaration has an identical signature and body;
   the public theorem signature is byte for byte identical, as is its node's
   recorded Lean statement. All three public imports are unchanged. The only
   file-level elaboration changes are the local scope and instance commands
   documented in the existing change record. Verdict: no accidental interface,
   definition, hypothesis, conclusion, or visibility change.
2. Read the complete module and compiled it independently with `lcompile.py`:
   no errors or warnings (44.3 seconds). A scratch copy with `#print axioms
   AlgebraicGeometry.ProEtale.integral_lfp_local_torsion_charts` compiled in
   38.1 seconds and printed only `propext`, `Classical.choice`, `Quot.sound`,
   and the permitted transitive `sorryAx` from still-open upstream statements.
   The delivered source contains no `sorry` or forbidden declaration mechanism.
   The new isomorphism definitions construct their maps and inverse laws;
   none selects an arbitrary object from an unproved existence theorem.
   Verdict: the single local hole is closed, with zero holes added.
3. No statement or module was split off, so there are no new open statements
   to validate or take over. Checked the new proved helpers' assumptions and
   edge cases: zero scalar for torsion charts, zero finite-free rank, empty
   schemes and open covers, and zero source or target ranks. A nonzero pivot
   forces positive source and target ranks; its complementary source rank is
   strictly smaller. The bound on a common refinement is the maximum of the
   two bounds. Verdict: no disguised restatement or unsupported construction.
4. Checked the proof from the final transports through presentation charts,
   matrix induction, and cyclic charts. The rationally invertible pivot
   comparison gives precisely the induction hypothesis on the Schur
   complement; exact pullback and the set-pullback isomorphism give the two
   distinct pullbacks of the original conclusion. Searched the library with
   alternate scalar-image/torsion/free queries and ran a fresh LeanFinder
   query; found no existing theorem that replaces the chart assembly. Read
   `dag/units/sk-thm-properbasechange.json`, including `realized`: this change
   is below its prescribed route and bypasses none of its statement or step
   nodes. All imports added for the new proof are proof-only. The removed
   geometric-evaluation dependency is the only old `proof_deps` edge removed.
   Verdict: the route and pruning are sound; no module leaves the closure.
5. Compared the node diff: only `proof`, `proof_deps`, and `proof_origin`
   change. The union of the proof steps' `uses` equals `proof_deps`. Checked
   the analytic-cover, matrix-entry, finite-biproduct split, rational pivot,
   coefficient restriction, and set-pullback interfaces against their uses.
   The node describes the actual induction rather than an unconstructed
   simultaneous diagonalization. Verdict: the node agrees with Lean, with
   no new nodes or statement changes.

Second-reading changes: corrected `## No longer needed` to enumerate the
three removed redundant direct proof imports and distinguish those removals
from closure pruning; appended this independent review. No Lean or node repair
was necessary.


## Second reading by A4

1. Compared the complete sandbox module and node with the read-only repository.
   The existing theorem signature is byte for byte unchanged; no existing
   declaration is removed or has a changed signature or visibility. The
   pre-existing helper proofs and constructions, including
   `resolutionRationalLF`, are unchanged. All three public imports are
   unchanged. The file-local scope and instance changes are covered by
   `coord/changes/integral-lfp-local-torsion-proof-environment.md` and do not
   alter exported data or statements. Verdict: no accidental interface change.
2. Independently compiled the delivered file with `lcompile.py`: no errors or
   warnings, 37.7 seconds. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.ProEtale.integral_lfp_local_torsion_charts`: 39.2 seconds,
   with only `propext`, `Classical.choice`, `Quot.sound`, and transitive
   `sorryAx` from still-open dependencies. Read the whole module and searched
   for forbidden declaration mechanisms and holes: none occur. The new
   isomorphisms construct maps and inverse laws; there is no definition
   choosing arbitrary data from an unproved existence theorem. Verdict:
   the one original local hole is closed and zero holes are added.
3. There are no split-off statements or modules. Checked the proved helpers
   in the zero scalar, zero free rank, zero matrix, zero source or target
   rank, and empty-scheme cases. The pivot indices force positive ranks;
   its complement has strictly smaller source rank. The torsion case has
   zero scalar image and the original finite constant quotient, and common
   refinements use the maximum of the two bounds. Verdict: no false edge
   case, disguised restatement, or new unsupported construction found.
4. Read the proof from the final theorem through presentation transport,
   strong matrix induction, binary chart gluing, and cyclic constant-norm
   charts. Checked that rational pivot invertibility supplies precisely the
   smaller matrix's rational local freeness, and that the final image and
   underlying-set inverse-image comparisons match the two conclusions.
   Fresh alternate searches with `rg` over the library and LeanFinder for
   local finite-free scalar images and finite constant scalar cokernels
   found no replacement theorem; the semantic hits concern generic sheaf
   finite presentation. Read the unit's `realized` statement and steps:
   this node-level assembly bypasses none of them. Added imports are
   proof-only. The three redundant direct imports and the sole removed old
   proof edge are fully listed above; no module is pruned from the closure.
   Verdict: route, imports, and pruning record are sound.
5. Compared the node record with Lean and checked every dependency's recorded
   interface. Only `proof`, `proof_deps`, and `proof_origin` change, the
   proof-step `uses` union equals `proof_deps`, and the recorded Lean
   signature remains unchanged. The proof now records actual binary pivot
   induction rather than an unconstructed simultaneous diagonal form.
   Verdict: DAG and Lean agree; no new nodes are needed.

Second-reading changes: appended this current independent review and recorded
fresh compilation, axiom, signature, edge-case, search, and DAG checks. No Lean
proof or node repair was necessary. The first dry run refused only the absent
current second-reading section; this section supplies it.
