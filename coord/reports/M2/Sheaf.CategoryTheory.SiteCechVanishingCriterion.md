## What changed

Added `Sheaf.CategoryTheory.SiteCechVanishingStep`, whose named intermediate theorem isolates the injective-resolution/dimension-shifting part and is left as one documented `sorry`. Replaced the target theorem's proof with a complete strong-induction argument using that intermediate theorem. Added the corresponding DAG node.

## Proved and sorry left

`CategoryTheory.Sheaf.isZero_H'_of_siteCech_vanishing` is proved by strong induction on the positive degree. The intermediate theorem `CategoryTheory.Sheaf.siteCech_vanishing_dimension_shift` remains `sorry` (node `lem-weil-pbc-site-cech-vanishing-dimension-shift`).

## No longer needed

No imports from the target module were removed; all existing imports remain available for the unresolved intermediate theorem. The target proof itself uses only the new step module in addition to the existing imports.

## Where the brief, the DAG or earlier work was wrong

The seven-step DAG proof requires substantial derived-functor and Čech-complex constructions that are only stated as postponed theorems. The unresolved portion is therefore isolated as a strict dimension-shifting interface rather than leaving an anonymous partial proof.

## New nodes

`lem-weil-pbc-site-cech-vanishing-dimension-shift` records the unresolved injective-resolution and dimension-shifting construction and its source in Stacks Tag 03F9.

## Earlier second reading (a previous round; superseded)

Second reader should verify the induction and the dimension-shifting interface before landing.

## Second reading by M2

1. **Statements and accidental changes.** I compared both delivered modules with the
repository versions. The existing target declaration is byte-for-byte unchanged; the
only target change is its proof. The added declaration has the same hypotheses as the
target and concludes the strictly intermediate base case plus one-step dimension shift.
Verdict: no target statement or existing declaration was weakened or changed.

2. **Proof and axioms.** Both modules compile with `lcompile.py --all`. The target proof
is a complete strong-induction argument: it handles degree one directly and applies the
dimension-shift implication to `p - 1` for `p > 1`. The only remaining `sorry` is the
named theorem `CategoryTheory.Sheaf.siteCech_vanishing_dimension_shift`, documented
above and represented by its DAG node; there is no `sorry` in a definition or any
forbidden declaration. Verdict: the proved target has no additional proof hole.

3. **New statement and prior declarations.** I searched the library and the recorded
LeanSearch, LeanFinder, Loogle, and grep results. No existing declaration states this
site Čech dimension-shifting interface. Its conclusion is weaker than the target and
is exactly the induction interface used by the target proof. Verdict: the split-off
statement is true by the cited Stacks 03F9 argument and is no broader than needed.

4. **Pruning and route.** The unit route is retained: the new theorem is the named
dimension-shifting step below the unit statement, and the target still imports and uses
it. No import can be removed while the unresolved theorem remains in its own module;
the existing imports are therefore retained. Verdict: no unjustified route bypass or
unreported pruning.

5. **DAG agreement.** The new node records the exact Lean declaration, source, proof
origin, statement, and module. The target node's proof now uses the new declaration,
while the new theorem is the sole documented split-off `sorry`. Verdict: the DAG and
Lean agree.

I changed only this report section during second reading; no Lean proof or statement
needed repair after compilation and comparison.
