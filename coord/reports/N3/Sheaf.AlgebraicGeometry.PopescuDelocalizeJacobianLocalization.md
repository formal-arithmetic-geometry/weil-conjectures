## What changed

Added `Sheaf.AlgebraicGeometry.PopescuAuxiliarySubmersivePresentation`, recording the explicit finite submersive presentation used by the Jacobian localization proof. The target theorem now obtains that presentation and applies `SubmersivePresentation.isStandardSmooth`.

## Proved and sorry left

`Algebra.popescu_auxiliary_isStandardSmooth` is proved from the named intermediate theorem. The intermediate theorem `Algebra.popescu_auxiliary_submersivePresentation` remains as one documented `sorry`, with node `popescu-auxiliary-submersive-presentation`.

## No longer needed

The original universal-property, polynomial-ring, partial-derivative, and standard-smooth proof dependencies are no longer imported directly by the target proof; the explicit presentation theorem encapsulates that calculation.

## Where the brief, the DAG or earlier work was wrong

The planned direct construction is substantially longer than the available formal library interface. The proof was decomposed into the strictly stronger explicit `SubmersivePresentation` statement, from which standard smoothness follows by the Mathlib theorem.

## New nodes

`popescu-auxiliary-submersive-presentation` records the explicit finite presentation and its Jacobian-unit argument.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the target proof compiles and preserves the target signature.

## Second reading by N3

1. **Interface and accidental changes.** I compared the delivered target module with the repository version. The theorem signature and its documentation are byte-for-byte unchanged; the only target change is replacing its proof with an application of the new intermediate theorem. The added auxiliary module and node are the only additional artifacts, and no declaration outside this delivery is adapted.

2. **Compilation and proof status.** I compiled both sandbox modules with `lcompile.py --all`; both compile without errors or warnings. The target has no `sorry`. The only remaining `sorry` is the named theorem `Algebra.popescu_auxiliary_submersivePresentation`, which is documented and represented by node `popescu-auxiliary-submersive-presentation`. An axioms probe reports only the permitted base axioms together with `sorryAx` from that split theorem.

3. **Statements and split-off theorem.** I checked the auxiliary statement against the target's hypotheses and conclusion and searched the project and Mathlib-facing search tooling for an existing declaration; no duplicate was found. The auxiliary theorem is a strictly more explicit presentation assertion, and the target follows from `SubmersivePresentation.isStandardSmooth`; it does not weaken or alter the target statement. Its proof source, natural-language argument, and DAG node agree. The theorem is intentionally the sole open split statement.

4. **Pruning and imports.** The auxiliary presentation module is imported privately because it is needed only by the proof. `Mathlib.RingTheory.Smooth.StandardSmooth` remains public because `IsStandardSmooth` occurs in the theorem type. The former direct universal-property, polynomial, derivative, and smoothness dependencies are not imported by this target proof and are recorded as no longer needed. No definition was changed, and no hollow definition or forbidden declaration was introduced.

5. **Unit route.** The node keeps chapter `sec-proper-base-change` and unit `sk-thm-p1`; the unit's `realized` statement and steps are untouched. The proof uses the explicit presentation intermediate on the planned Jacobian step and then the Mathlib standard-smoothness theorem, so the unit route metadata remains intact.

**Changes made in this second reading:** added this review record (and synchronized the delivery report under `coord/reports/N3/`); no Lean source or DAG correction was necessary.
