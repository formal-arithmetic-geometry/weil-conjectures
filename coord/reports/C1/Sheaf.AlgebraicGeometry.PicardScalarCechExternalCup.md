## What changed

Repaired reviewer X-2527f, E1/E2 point 4, exactly as requested. In
`lean/Sheaf/AlgebraicGeometry/PicardScalarCechExternalCup.lean`, removed the
entire docstring and declaration `picardScalarCech_externalCup_core` and
replaced the covered theorem's proof through it with `sorry`. The covered
signature, complete proof docstring, imports and visibility are unchanged.

Updated both affected DAG records: the retired core has no Lean declaration
or purported proof, and the covered node retains its source-based proof plan
with explicit use of cover equalities and an unresolved proof origin.
The change is documented in
`coord/changes/picardScalarCech_externalCup_core.md`.
Removed the obsolete second-reading section; the second reader must review
this repaired version before delivery.

## Proved and sorry left

No theorem is newly proved. One false holed declaration is removed, and the
covered theorem's hole is restored; this is a correctness repair, not proof
progress or a decomposition. Zero statements are split off.

The sole remaining local sorry is
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup`
(node `lem-sc-picard-scalar-cech-external-cup`). The covered theorem is now the
explicit unresolved proof obligation. No other module gains a sorry.

Validation is performed with `lcompile.py` and `deliver3.py --no-push`.
The next worker performs the independent second reading; nothing is pushed
by this worker.

## No longer needed

Removed declaration:
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`, with node
`lem-sc-picard-scalar-cech-external-cup-core`. The covered theorem no longer
uses the false uncovered core. No import or module is removed, and no unit
step is bypassed. No new node replaces the core.

## Where the brief, the DAG or earlier work was wrong

The earlier repair merely marked the core disputed while retaining it and the
covered theorem's application of it. That did not fix the false dependency.
The uncovered core is false because resolution comparison equations need not
uniquely determine comparison witnesses without cover hypotheses.

Counterexample: R = Q[t], A = R[t^-1], F associated to A direct-sum (A/R),
U = {D(t)}, Y = Spec Q, G = O_Y and the full singleton cover of Y. Choose
eX(x) = (x,0) and eP(x) = (x,[x]). These R-linear maps satisfy the comparison
equations for every resolution because the quotient summand restricts to
zero on D(t). At p = q = n = 0, with x = t^-1 and the other factor 1, the
claimed equality has left side (x,[x]) and right side (x,0); [t^-1] is nonzero.
Thus the entire uncovered assertion is retired. The covered theorem's cover
equalities exclude this counterexample, but its proof remains unresolved.
All downstream statements are unchanged.

## Second reading by C1

1. **Visible declarations and signatures.** Compared the delivered module with the repository version. The covered theorem `picardScalarCech_externalCup` has byte-for-byte identical statement, imports, and visibility. The only declaration change is removal of the retired false core, documented by the existing change record; no target statement was changed.

2. **Compilation and proof status.** Compiled `lean/Sheaf/AlgebraicGeometry/PicardScalarCechExternalCup.lean` with `lcompile.py`; it succeeds without errors. The covered theorem remains the sole explicit `sorry`; there are no sorries in definitions and no axioms, unsafe, opaque, extern, or implemented_by declarations. The retired core has no Lean declaration.

3. **Statements and split nodes.** No new statement is introduced and no statement is split off. The removed core node records the counterexample and retirement; the covered node retains its original statement and unresolved source-based proof plan. The remaining theorem is exactly the declared target and is not weakened.

4. **Shortest route and pruning.** The previous proof's application of the uncovered core was unsound because cover hypotheses are needed to determine comparison witnesses. I verified that the repaired theorem no longer references that core. No additional Mathlib or upstream theorem closes the covered obligation, and no imports can be removed safely. The retired core is listed under `## No longer needed`; the unit route remains represented by the covered node and its proof dependencies.

5. **DAG and unit agreement.** The covered node's Lean declaration, proof dependencies, and proof origin agree with the repaired module. The retired core node has no `lean` declaration and records the false uncovered assertion and its counterexample. The unit `sk-prop-av-cube` is not bypassed; no realized unit step was removed.

Changed in this second reading: added this review section only. The earlier repair removing `picardScalarCech_externalCup_core` and restoring the covered theorem's `sorry` is retained, together with its change record and DAG updates.
