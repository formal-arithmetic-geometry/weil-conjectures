## What changed
Added the comparison import and reduced the target theorem to the stalk-based constructibility predicate using `isConstructibleEtaleModuleSheaf_iff`. Added the core intermediate theorem declaration, whose proof remains postponed.

## Proved and sorry left
`isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant` is proved by a real application of `isConstructibleEtaleModuleSheaf_iff` and the core theorem. `isConstructibleSheaf_etaleLowerShriek_constant_core` remains `sorry`; node `lem-weil-pbc-etale-free-sheaf-constructible-core` records the stratification, base-change, finite-etale comparison, and pushforward argument.

## No longer needed
No imports were removed. The existing proof-plan imports are retained as dependencies of the core theorem.

## Where the brief, the DAG or earlier work was wrong
The final conversion from finite locally constant module values to `IsConstructibleEtaleModuleSheaf` is exactly the existing comparison theorem, so it should be used explicitly.

## New nodes
`lem-weil-pbc-etale-free-sheaf-constructible-core` is the strictly intermediate stalk-based constructibility statement.

## Earlier second reading (a previous round; superseded)
The target statement is unchanged and its proof is a direct application of the established comparison equivalence. The new core statement is strictly an intermediate stalk-based constructibility result and matches the postponed geometric argument.

## Second reading by T1

1. **Statements and accidental changes.** Compared the delivered module byte-for-byte with
   the repository version. The existing target declaration is unchanged; the only additions
   are the proof-only comparison import, the intermediate core declaration, and the target
   proof. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no errors
   and the only remaining `sorry` is the named core theorem. The target proof is a direct
   application of `isConstructibleEtaleModuleSheaf_iff`; no forbidden declarations occur.
   Verdict: pass, with the core theorem intentionally split off under its node.
3. **Split-off statement.** Checked that the core statement is strictly stalk-based,
   matches the geometric reduction, has a source/docstring, and has the corresponding DAG
   node. It does not restate the target. Verdict: pass.
4. **Pruning and route.** The comparison import is proof-only and is plain `import`; all
   existing proof-plan imports remain needed by the split core argument. The unit remains
   `sk-thm-p1` and its route is preserved. Verdict: pass; no nodes or imports pruned.
5. **DAG agreement.** The core node's declaration, statement, proof dependencies, source,
   and split status agree with the Lean file; the target node records the direct comparison
   route. Verdict: pass.

Changed the long `IsConstructibleSheaf` line to satisfy the 100-character style limit.
