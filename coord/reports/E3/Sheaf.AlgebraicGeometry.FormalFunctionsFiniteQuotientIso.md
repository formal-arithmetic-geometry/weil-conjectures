## What changed

The target theorem now combines two strict intermediate theorems. `FormalFunctionsFiniteQuotientIsoB` supplies the quotient-system isomorphism and its finite-level factorization. `FormalFunctionsFiniteQuotientIsoR` supplies the linear maps and their two component formulas, conditional on that factorization. The target proof is the real Lean composition of these results.

## Proved and sorry left

The target `AlgebraicGeometry.formalFunctions_finite_quotient_iso` is proved. The two decomposition theorems remain named `sorry`s: `AlgebraicGeometry.formalFunctions_finite_quotient_iso_b` and `AlgebraicGeometry.formalFunctions_finite_quotient_iso_r`, with their new nodes listed below.

## No longer needed

None. All original proof imports remain available to the two intermediate statements.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked by a missing compiled dependency cache. Rebuilding the local source set repaired that infrastructure issue. The original proof plan is retained as two strict intermediate statements.

## New nodes

`lem-weil-pbc-formal-functions-finite-quotient-iso-b` and `lem-weil-pbc-formal-functions-finite-quotient-iso-r` are added for the two named intermediate theorems.

## Earlier second reading (a previous round; superseded)

The target proof composes the two strict intermediate statements. The new statements are exactly the interfaces used by the target and each is a proper sub-result of the original theorem.

## Second reading by E3

1. **Interface preservation.** Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and proof-only imports changed. Verdict: pass.
2. **Compilation and axioms.** Compiled B, R, and the target with `lcompile.py --all`; all compile cleanly. The target has no `sorry`; the only remaining sorries are the two named split theorems, each with a docstring and DAG node. Verdict: pass.
3. **Statements and split nodes.** Checked both split declarations against their node statements and the target's original statement. B supplies the quotient-system isomorphism and factorization; R strictly takes such a factorization as input and constructs the linear maps. Both are true interfaces strictly below the target and preserve the unit route. Verdict: pass.
4. **Pruning and proof route.** The target proof uses exactly B and R. Removed the target's now-unused proof imports (`QuotientBaseChangeIdeal`, `ClosedImmersionUnitQuotient`, `AffineMorphismCohomologyEdge`, `ModuleCohomologyFMapFunctorial`, and `ModuleCohomologyFMapBasicProperties`); these remain available through B. Updated the target node proof and `proof_deps` to the two split nodes. Verdict: pass.
5. **DAG and unit agreement.** The two new nodes have source, proof plan, dependencies, Lean records, chapter, and unit metadata. The target node now records the actual composition route; the unit `sk-thm-p1` route is retained through B and R. Verdict: pass.

Changed the report, target DAG proof metadata, and removed five redundant target imports. No statement or definition was changed.
