## What changed

Proved `AlgebraicGeometry.Scheme.etaleModule_enoughInjectives` by applying
`etaleModuleSheaves_grothendieckAbelian` and installing the resulting Grothendieck abelian
instances, then using Mathlib's `IsGrothendieckAbelian.enoughInjectives` instance. Added a
proof-only import of `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.

## Proved and sorry left

The sole declaration `etaleModule_enoughInjectives` is proved. No `sorry` remains in the
item or in added files.

## No longer needed

None beyond the existing proof dependencies; the DAG route through Grothendieck abelianness
and the enough-injectives theorem is retained.

## Where the brief, the DAG or earlier work was wrong

No errors found.

## Second reading by Q2

1. **Visible declarations and statements.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; the only code difference is a proof-only import and the proof body.

2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations in the delivered file. A scratch `#print axioms` reports only the permitted logical axioms together with `sorryAx` inherited from the still-open Grothendieck-abelian dependency.

3. **Statements and searches.** No statement was split off or added. The existing theorem is proved directly from `etaleModuleSheaves_grothendieckAbelian` and Mathlib's `IsGrothendieckAbelian.enoughInjectives`; no duplicate declaration was introduced.

4. **Route and pruning.** The proof follows the unit route: establish Grothendieck abelianness for the module-sheaf category and abelian-sheaf category, then apply the generic enough-injectives instance. All existing proof dependencies remain used, and the added import is proof-only.

5. **DAG agreement.** The node's theorem, proof dependencies, and proof origin agree with the implementation. The unit's realized route is unchanged.

No repair was necessary beyond the worker's proof and proof-only import; no imports or nodes were pruned.
