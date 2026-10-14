## What changed

Replaced the proof of
`AlgebraicGeometry.affineModelLimitHomEquation_of_coherent_objects` in
`Sheaf.AlgebraicGeometry.AffineModelLimitHomEquationOfCoherentObjects`.
Unfold only the named limit Hom transport, retain both supplied object triangles,
and generalize the fixed `perfectHomComparison` simultaneously in those triangles
and the goal. This avoids expensive kernel conversion through its explicit
composition construction. Instantiate the already proved `AlgebraicGeometry.affineModel_scalarConjugation_nat`
with the cocone ring maps, the localized tilde functors, the geometric derived
pullback, the supplied natural comparison `m.θlim j`, and the two object triangles
`(m.hlim j).1` and `(m.hlim j).2`. The result is the required equation because
`perfectLimitMap` is the same conjugation along `affineModelLimitArrow`.
The single-file check via `lcompile.py` passes without warnings in 18.5 seconds.
All signatures, visibility, imports and definitions are unchanged. The existing
DAG plan is implemented directly; no change of route or new node is needed.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.affineModelLimitHomEquation_of_coherent_objects`
(node `lem-pc-affine-model-limit-hom-equation-of-coherent-objects`).
No holes added, no split statements, and no `sorry` remains in the delivered module.
The existence theorem for coherent comparisons is not applied: the proof uses
the supplied structure and the already proved categorical conjugation lemma.

## No longer needed

None. No imports removed and no planned dependency node or module pruned.
The coherent-object definitions, scalar-extension map and perfect Hom transport
remain necessary. The comparison-data constructor is not applied by this proof,
but its existing public import is preserved to keep the module interface unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The generic scalar-conjugation argument is
already proved in the coherent-object module, so it need not be repeated here.
The unit's route is unchanged.

## Second reading by U2

1. Compared the delivered module with the repository version. The declaration signature, imports, visibility, definitions, and all existing statements are byte-for-byte unchanged; only the target proof body differs. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. Checked the sole target and its proof dependencies against the library and DAG. No split-off statements or new nodes were added, and no duplicate theorem was introduced. The proof uses the existing scalar-conjugation theorem and supplied coherent-object triangles, and proves the unchanged target exactly. Verdict: pass.

4. Read the proof from the target downward and checked pruning. The direct `affineModel_scalarConjugation_nat` route is shorter than expanding kernels and uses no unnecessary import or dependency; no import or node can be removed. The unit route is preserved because the coherent comparison data and perfect Hom transport remain the stated interfaces. Verdict: pass.

5. Checked the DAG node's statement, proof, proof dependencies, and proof origin against the Lean proof. They agree, and the realized unit route is unchanged. Verdict: pass.

Changed after second reading: no mathematical or interface changes; only this second-reading record was added to the report.
