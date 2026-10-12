## What changed

Proved `Algebra.exists_unramified_conormal_polynomial_chart` in
`lean/Sheaf/RingTheory/ConormalChartUnramifiedLocalization.lean`, with its signature and
existing docstring unchanged. Added a proof-only import of
`Mathlib.RingTheory.Etale.Kaehler`. Nakayama is already available transitively.

A fully proved private polynomial chain-rule helper supports the Jacobian calculation.
The proof works in the quotient of the relative differential module by its augmentation-ideal
multiples, kills the coordinate differentials there, applies Nakayama, and localizes the
annihilated module. No data is defined from an unproved existence theorem.

The existing node's proof and proof dependencies now describe this actual Lean argument.
No unit statement or realized step is bypassed.

## Proved and sorry left

Closed the sole original hole:
`Algebra.exists_unramified_conormal_polynomial_chart`
(node `lem-weil-pbc-conormal-chart-unramified-localization`).

Added no holes. No `sorry` remains in the delivered module.
The private helper `Algebra.conormal_polynomial_chain_rule` is also proved.

Single-file compilation passes without warnings. The argument needs no nonempty index set,
nonzero ring, smoothness or conormal-basis hypothesis. All sums and polynomial inductions
work for zero variables and zero equations. The delivery dry run checks every added
constant's axioms; only the permitted standard axioms occur.

## No longer needed

No existing import was removed. The second reader removed the redundant added import
`Mathlib.RingTheory.Finiteness.Nakayama`; compilation without it succeeds. The planned proof dependency
`lem-weil-pbc-polynomial-ring-kahler-basis` and its proposed module
`Mathlib.RingTheory.Kaehler.Polynomial` are not needed by this proof: direct polynomial
induction proves the chain rule. They were never imported into the original module.
Removed that node from this item's `proof_deps`; other users may still need it.

The Nakayama and differential-localization nodes remain needed and are used through their
recorded Mathlib declarations. No additional Sheaf proof dependency is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG's polynomial differential-basis route
was longer than necessary. Using the kernel of constant coefficient as the augmentation
ideal avoids proving a separate equality with the ideal spanned by the variables.

The localization's canonical scalar-action instances require an explicit self scalar-tower
instance and equality of algebra structures; these are proved locally without changing any
library interface or instance.

## Second reading by Q1

1. **Interfaces: pass.** Read the repository and sandbox modules and their full diff.
   The sole existing declaration's signature and docstring are byte for byte unchanged:
   arbitrary commutative R, n and c, f and a, precisely the Jacobian right-inverse ha,
   and the same explicit theta and localization algebra structure. There are no
   definition changes or change records. The only new declaration is a private proved
   chain-rule helper. All added imports are proof-only.
2. **Kernel proof: pass.** Independently compiled the module through lcompile.py without
   errors or warnings. A scratch copy with `#print axioms` for the public theorem and
   private chain-rule helper prints exactly propext, Classical.choice and Quot.sound
   for each. Scanned the delivered Lean for sorry and prohibited declarations/options:
   none occur. Local constructions are concrete quotient modules, derivations and
   algebra maps, not data chosen from an unproved existence theorem.
3. **Split statements and edge cases: pass.** No split-off statements, new holes or new
   nodes. Read the helper's polynomial induction: constants and addition are immediate;
   multiplication by X uses Leibniz and the delta sum. It handles Fin 0 and arbitrary
   commutative coefficient rings. For c = 0 the coordinate correction is the original
   quotient map and all differential generators vanish. For n = 0 and c > 0, ha forces
   0 = 1 in C, so the zero-ring case remains covered. For n = c = 1, f = X and a = 1,
   theta sends X to -y and the resulting chart is unramified, as the signs predict.
   Searched Mathlib's polynomial Derivation/PDeriv and Kaehler modules and the library's
   RingTheory files with chain-rule/derivation/pderiv terms, and ran msearch Loogle with
   `Derivation, MvPolynomial.pderiv`: derivative primitives but no matching composed
   chain-rule or entire chart theorem. No duplication requiring a new public lemma.
4. **Route and pruning: pass.** Read Stacks 07CH online (the local smoothing.tex is absent),
   specifically its corrected-coordinate differential calculation and Nakayama paragraph,
   and dag/units/sk-thm-p1.json including realized. The proof kills dy using ha in
   M/(ker(constantCoeff) M), then dx, then coefficient and polynomial differentials.
   Universal differentials span M; finite type gives finite M; Nakayama gives g-1 in
   the kernel; differential localization makes the localized module zero. The explicit
   equality halg verifies precisely the algebra structure in the conclusion. The route
   is the source's differential/Nakayama route; replacing the polynomial basis by direct
   induction occurs below the unit level. Neither this node nor the removed basis node
   realizes a required unit step. The old proof_deps minus the new proof_deps is exactly
   lem-weil-pbc-polynomial-ring-kahler-basis, already listed above. The existing public
   imports support statement vocabulary; the new Etale.Kaehler import supplies localization.
   Removed the redundant added Nakayama import after compilation and axiom checks without it.
5. **Nodes: pass after repair.** Compared the existing node JSON with its repository version.
   Changes are confined to proof, proof_deps and lean; restored lean to the original record
   because the first worker accidentally encoded its statement as literal Unicode escapes.
   The three proof steps now match finite generation/chain rule, the quotient differential
   calculation, and Nakayama/localization. Read the differential-definition node and the
   Nakayama and localization nodes: the latter two record exactly the Mathlib declarations
   used by the proof. Their union with the differential-definition node is proof_deps;
   proof_origin correctly retains the source argument. No new node fields are needed.

Second reading changed only the redundant proof import, the corresponding report text,
and the escaped node lean.statement metadata. The proof itself needed no repair.
