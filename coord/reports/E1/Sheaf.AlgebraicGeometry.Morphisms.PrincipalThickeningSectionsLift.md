## What changed

Added `PrincipalThickeningSingleLift.lean`, defining the canonical composite of consecutive principal-thickening transitions and splitting the geometric lifting argument into `principal_thickening_single_lift`. The target module imports this theorem and proves the arbitrary `res` formulation by induction on its recursion laws.

## Proved and sorry left

The target theorem `AlgebraicGeometry.Scheme.principal_thickening_sections_lift` is proved. The new intermediate theorem `AlgebraicGeometry.Scheme.principal_thickening_single_lift` remains `sorry` (node `new-principal-thickening-single-lift`), containing the derived two-term-complex argument from Tags 0H3D and 0H3E.

## No longer needed

No stated imports were removed; both the finite-etale transfer import and the cohomology definitions remain available to the new intermediate theorem.

## Where the brief, the DAG or earlier work was wrong

The DAG's three geometric proof steps cannot be expressed using existing Lean declarations. The geometric core was therefore split into one strictly smaller theorem; the recursion from arbitrary `res` to the canonical composite is proved directly.

## New nodes

`new-principal-thickening-single-lift` records the geometric single-lift intermediate theorem and its source.

## Second reading by E1

1. **Interface and accidental changes.** I compared the delivered target module with the
repository copy. The theorem signature and all existing declarations are byte-for-byte
unchanged; the only target-module changes are the proof and a proof-only import. The new
module and node are the declared split-off addition.

2. **Compilation and proof status.** I compiled both sandbox modules with
`lcompile.py --all`; they compile cleanly. The target theorem
`AlgebraicGeometry.Scheme.principal_thickening_sections_lift` has no `sorry`. The only
remaining hole is the explicitly named `principal_thickening_single_lift`, documented in
its docstring and represented by `new-principal-thickening-single-lift`.

3. **Statement and node review.** The split-off statement is the canonical fixed-gap
lifting core, strictly smaller than the parent because it removes the arbitrary `res`
family and its recursion laws. Its hypotheses and conclusion match the Lean declaration,
and the node records its source, proof route, module, and declaration. No existing library
declaration duplicates it.

4. **Proof route and pruning.** The parent proof uses the split-off theorem and proves the
`res` recursion by induction, with the base and successor equations checked directly.
The canonical composite definition is used at each induction step. Both public imports are
needed by the statements or the split-off theorem, so no import or proof dependency can be
pruned.

5. **Unit route.** The parent remains the node realizing the principal-thickening lifting
statement in `sk-prop-input-spreading`; the split-off theorem records the first geometric
step and does not bypass the unit's route. The delivery is therefore mathematically and
structurally consistent with the DAG.

The second reading found no changes necessary beyond this report section.
