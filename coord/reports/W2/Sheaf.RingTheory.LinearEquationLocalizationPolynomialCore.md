## What changed
Replaced the proof of `MvPolynomial.linearEquationLocalizationPolynomialCore` in
`lean/Sheaf/RingTheory/LinearEquationLocalizationPolynomialCore.lean`. The evaluation map
is injective because explicit elimination of the distinguished variable yields a left inverse
through the quotient and localization universal properties. It is surjective because the
relation expresses the distinguished variable in its image, polynomial induction gives every
quotient class, and localization denominators come from constant polynomials over Af.
`AlgEquiv.ofBijective` supplies the equivalence; `aeval_X` and the inverse law give the
inverse values on free variables. The proof compiles without warnings.

## Proved and sorry left
Closed the one original hole: `MvPolynomial.linearEquationLocalizationPolynomialCore`
(blueprint: `lem-weil-pbc-linear-equation-localization-polynomial-core`).
No holes remain and no holes were added. The delivery is a complete proof, not a decomposition.
The delivery tool checks the declaration's axioms.

## No longer needed
None. No imports removed, no new imports, and no planned dependencies bypassed.
Temporary decomposition modules were removed from the sandbox before delivery.

## Where the brief, the DAG or earlier work was wrong
No mathematical or interface errors found. The DAG's construction works with the polynomial,
quotient, and localization universal properties already in Mathlib. No signature or visibility
changes, new nodes, or forced adaptations. The proof handles a zero coefficient (the localized
rings are zero), the zero ring, and one variable; no nontriviality or nonzero hypotheses are used.

## Second reading by W2

1. I compared the delivered module with the repository version. The theorem signature is byte for byte unchanged; only the proof body replaces `sorry`. The proof establishes the stated Af-algebra equivalence for every commutative ring, including zero coefficients, zero rings, empty and singleton variable sets, with no added hypotheses.

2. The module compiles cleanly through `lcompile.py`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definitions. The proof constructs an injective evaluation map using a localization lift and a left inverse, and constructs surjectivity by polynomial induction and localization surjectivity. The final equivalence is `AlgEquiv.ofBijective`; no new theorem is split off.

3. The statement and proof dependencies agree with the node. The existing Mathlib declarations used are the polynomial evaluation, quotient, and localization universal-property APIs recorded by the node. I searched the repository and the recorded LeanFinder, Loogle, and grep searches; no existing declaration supplies this elimination equivalence.

4. The proof follows the unit route: evaluation, factoring through the linear relation, extension across localization, then generator and polynomial induction arguments. No unit step or required dependency is bypassed, and no import is unused or removable.

5. The node metadata matches the Lean declaration and proof: `proof`, `proof_deps`, and `proof_origin` describe the evaluation/localization construction, and the realized unit remains `sk-thm-p1`. Edge cases are covered uniformly by the ring and finite-index APIs.

I changed only the proof body and added this second-reading record. No statements, definitions, imports, nodes, or dependency records required repair.
