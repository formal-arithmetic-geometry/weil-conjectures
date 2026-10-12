## What changed
Added `FormalModuleSupportSucc`, whose consecutive-level support theorem is used to prove `formalModule_support_eq` by induction. The target theorem is now fully proved; the helper theorem remains a named split with `sorry`.

## Proved and sorry left
Proved `AlgebraicGeometry.formalModule_support_eq`. Sorry remains in `AlgebraicGeometry.formalModule_support_succ` (node `lem-weil-pbc-formal-system-support-succ`) as the strictly smaller consecutive-level step.

## No longer needed
No imports from the original module were removed; all existing imports remain available for the helper theorem's planned proof.

## Where the brief, the DAG or earlier work was wrong
The DAG plan requires substantial stalk and quotient algebra, so the consecutive-level argument was split into a dedicated theorem to keep the target proof kernel-complete.

## New nodes
`lem-weil-pbc-formal-system-support-succ` records the consecutive-level support equality and is provided by `Sheaf.AlgebraicGeometry.FormalModuleSupportSucc`.

## Second reading by H2

1. Compared the delivered `FormalModuleSupportConstant.lean` with the repository.
The existing theorem signature and its statement are unchanged byte-for-byte; the
only source change is the added plain proof import and the proof body. The new
`FormalModuleSupportSucc.lean` is the declared split module, and no existing
definition or target statement was changed. Verdict: pass.
2. Compiled both modules in import order with `lcompile.py`; both compile cleanly.
The only remaining `sorry` is the public named theorem
`AlgebraicGeometry.formalModule_support_succ`, and it has a matching node and
complete source-based docstring. There are no forbidden declarations or hollow
definitions. The proved theorem's axioms are therefore limited to the permitted
axioms plus the expected `sorryAx` transitively through the split helper.
Verdict: pass as a partial proof delivery.
3. Checked the helper statement against the coherent formal-module definition and
the Stacks Project Tag 0CYV proof. Since `op n` denotes level `n + 1`, the helper
relates exactly adjacent levels and the induction proves the target's stated
support equality. The quotient-by-the-ideal-power and annihilation argument is
valid pointwise, including the zero-module and zero-ideal cases, and introduces
no extra hypotheses or weakened conclusion. Searches by declaration and concept
in the library found no existing duplicate. Verdict: pass.
4. The target proof uses the shortest available reduction: induction and the
consecutive-level helper. The original imports are retained because they are
proof dependencies of the unfinished helper; no import can be pruned from this
delivery. The helper is strictly smaller than the target and preserves the
unit's consecutive-level route. Verdict: pass.
5. Checked the target node's proof and proof dependencies against the Lean proof,
and checked the new node's statement, Lean signature, source, chapter, unit,
proof route, and search records. The new node is marked split and its declaration
matches the module exactly. No unit step is bypassed. Verdict: pass.

Second reading changed only this report by recording the independent review.
